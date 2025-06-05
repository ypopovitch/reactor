Require Import Reals.
Require Import Coquelicot.Coquelicot.

Local Open Scope R_scope.

Record ReactorState := {
  keff : R -> R;
  T_core : R -> R;
  T_coolant : R -> R;
  rods_pos : R -> nat;
  poison_c : R -> R;
  P_core : R -> R;
  P_out : R -> R;
  P_out_target : R -> R;
  time : R
}.

(* physical constants *)

Definition keff_0 := 1.2. (* TODO *)
Definition alpha := 1. (* TODO *) (* reactivity gain / K around the reference state *)
Definition beta := 1. (* TODO *) (* reactivity gain / poison ppm around the reference state *)
Definition gamma := 1. (* TODO *) (* reactivity gain per cm of rod insertion *)
Definition epsilon := 1. (* TODO *) (* heat transfered from core to coolant in W / K *)
Definition zeta := 1. (* TODO *) (* heat transfered from coolant to secondary circuit in W / K  *)
Definition T_c0 := 300. (* TODO *) (* reference core temperature in °C  *)
Definition P_c0 := 1. (* TODO *) (* reference core power in W  *)
Definition poison_c0 := 300. (* TODO *) (* reference poison concentration in ppm *)
Definition C_core := 1. (* TODO *) (* core thermal capacity in J / K *)
Definition C_coolant := 1. (* TODO *) (* coolant thermal capacity in J / K *)
Definition T_ext := 1. (* TODO *) (* secondary circuit temperature in °C *)
Definition lambda := 1. (* TODO *) (* poison generation via fission in ppm / W *)
Definition mu := 1. (* TODO *) (* poison decay in ppm / s *)
Definition eta := 1. (* TODO *) (* rod insertion coefficient in cm / W *)

(* safety constants *) 

Definition core_overheating_threshold := 600. (* °C *)
Definition coolant_overheating_threshold := 100. (* °C *)

(* physical values evolution *)

Theorem T_core_derivable (s : ReactorState) : forall t, derivable_pt (T_core s) t.
Proof. Admitted.

Definition dT_core_dt (s : ReactorState) (t : R) : R :=
  derive_pt (T_core s) t (T_core_derivable s t).

Definition core_heat_balance_equation (s : ReactorState) (t : R) : Prop :=
  C_core * dT_core_dt s t = (P_core s t) - epsilon * ((T_core s t) - (T_coolant s t)).

Theorem T_coolant_derivable (s : ReactorState) : forall t, derivable_pt (T_coolant s) t.
Proof. Admitted.

Definition dT_coolant_dt (s : ReactorState) (t : R) : R :=
  derive_pt (T_coolant s) t (T_coolant_derivable s t).

Definition coolant_heat_balance_equation (s : ReactorState) (t : R) : Prop :=
  C_coolant * dT_coolant_dt s t = epsilon * ((T_core s t) - (T_coolant s t)) 
                                - zeta * ((T_coolant s t) - (T_ext)).

Definition keff_equation (s : ReactorState) (t : R) : Prop :=
  (keff s t) = (keff_0
              - alpha * ((T_core s t) - T_c0)
              - beta * ((poison_c s t) - poison_c0)
              - gamma * INR (rods_pos s t)).

Theorem poison_c_derivable (s : ReactorState) : forall t, derivable_pt (poison_c s) t.
Proof. Admitted.

Definition dpoison_c_dt (s : ReactorState) (t : R) : R :=
  derive_pt (poison_c s) t (poison_c_derivable s t).

Definition poison_balance_equation (s : ReactorState) (t : R) : Prop :=
  dpoison_c_dt s t = lambda * (P_core s t) - mu * (poison_c s t).

Definition P_core_expression (s : ReactorState) (t : R) : Prop :=
  P_core s t = P_c0 * ((keff s t) - 1).

Definition P_out_expression (s : ReactorState) (t : R) : Prop :=
  P_out s t = zeta * ((T_coolant s t) - (T_ext)).

(* rod control *)

Definition rod_control_expression (s : ReactorState) (t : R) : Prop :=

(* safety properties *)

Definition not_core_overheating (s : ReactorState) : Prop :=
  T_core s <= core_overheating_threshold.

Definition core_temperature_safety := is_invariant not_core_overheating.

Definition not_coolant_overheating (s : ReactorState) : Prop :=
  T_coolant s <= coolant_overheating_threshold.

Definition coolant_temperature_safety := is_invariant not_coolant_overheating.

Theorem safety : core_temperature_safety /\ coolant_temperature_safety.
