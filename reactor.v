Require Import Reals.

Local Open Scope R_scope.

Record ReactorState := {
  keff : R;
  T_core : R;
  T_coolant : R;
  pressure : R;
  rods_position : nat;
  poison_concentration : R;
  comb_consumption : R;
  cooling_efficiency : R;
  time : R
}.

Definition keff_nominal := 2.
Definition T_ref := 300. (* °C *)
Definition alpha := 14.
Definition core_overheating_threshold := 600. (* °C *)
Definition coolant_overheating_threshold := 100. (* °C *)

Inductive step_keff : ReactorState -> R -> Prop :=
  | step_keff_C1 : forall s,
    step_keff s (keff_nominal - alpha * ((T_core s) - T_ref)).

Inductive step_T_core : ReactorState -> R -> Prop :=
  | step_T_core_C1 : forall s r,
    step_T_core s r. (* TODO *)

Inductive step_T_coolant : ReactorState -> R -> Prop :=
  | step_T_coolant_C1 : forall s r,
    step_T_coolant s r. (* TODO *)

Inductive step_pressure : ReactorState -> R -> Prop :=
  | step_pressure_C1 : forall s r,
    step_pressure s r. (* TODO *)

Inductive step_rods_position : ReactorState -> nat -> Prop :=
  | step_rods_position_C1 : forall s n,
    step_rods_position s n. (* TODO *)

Inductive step_poison_concentration : ReactorState -> R -> Prop :=
  | step_poison_concentration_C1 : forall s r,
    step_poison_concentration s r. (* TODO *)

Inductive step_comb_consumption : ReactorState -> R -> Prop :=
  | step_comb_consumption_C1 : forall s r,
    step_comb_consumption s r. (* TODO *)

Inductive step_cooling_efficiency : ReactorState -> R -> Prop :=
  | step_cooling_efficiency_C1 : forall s r,
    step_cooling_efficiency s r. (* TODO *)

Inductive step : ReactorState -> ReactorState -> Prop :=
  | step_C1 : forall (s s' : ReactorState),
    step_keff s (keff s') ->
    step_T_core s (T_core s') ->
    step_T_coolant s (T_coolant s') ->
    step_pressure s (pressure s') ->
    step_rods_position s (rods_position s') ->
    step_poison_concentration s (poison_concentration s') ->
    step_comb_consumption s (comb_consumption s') ->
    (time s) + 1 = (time s') -> 
    step s s'.

Inductive reachable_from : ReactorState -> ReactorState -> Prop :=
  | Reach_self : forall s,
    reachable_from s s
  | Reachable_trans : forall s1 s2 s3,
    reachable_from s1 s2 ->
    step s2 s3 ->
    reachable_from s1 s3.

Inductive is_initial_state : ReactorState -> Prop :=
  | is_initial_state_C1 : forall s, is_initial_state s. (* TODO *)

Inductive reachable : ReactorState -> Prop :=
  | reachable_C1 : forall initial_state s,
    is_initial_state initial_state ->
    reachable_from initial_state s ->
    reachable s.

Definition is_invariant (P : ReactorState -> Prop) : Prop :=
  forall s, reachable s -> P s.

Definition not_core_overheating (s : ReactorState) : Prop :=
  T_core s <= core_overheating_threshold.

Definition core_temperature_safety := is_invariant not_core_overheating.

Definition not_coolant_overheating (s : ReactorState) : Prop :=
  T_coolant s <= coolant_overheating_threshold.

Definition coolant_temperature_safety := is_invariant not_coolant_overheating.

Theorem safety : core_temperature_safety /\ coolant_temperature_safety.
