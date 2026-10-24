-- Prove2me | Definitions.Def_PricingWithTips3DM_59253dea2fb8d974bdec5e81
-- name    : PricingWithTips3DM_59253dea2fb8d974bdec5e81
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T21:19:34.648916+00:00
-- url     : https://prove2.me/theorems/2664957b-6e79-40ec-98b4-478b8b079cf2
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Normalizer.BoundedReject
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_9f707d24e4f2a204cd302164
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Guarded circuit normalizer: bounded rejection composition
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

open Computability StateTransition
open _root_.Turing

private abbrev transition := flip Option.bind step

/-- A configuration reaches the canonical invalid record within a stated
number of concrete machine steps. -/
def RejectsIn (start : machine.Cfg) (bound : Nat) : Prop :=
  Nonempty <| StateTransition.EvalsToInTime step start
    (some (haltList machine [.invalidMark])) bound

/-- Exact cleanup packaged in the bounded evaluator interface. -/
theorem cleanup_rejectsIn (state : State) (input : List CircuitSym)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    RejectsIn
      (cfg (some .clearInput) state input output rows inputCount gateCount
        operand saved outputIndex)
      (clearAndEmitInvalidSteps input output rows inputCount gateCount operand
        saved outputIndex) := by
  exact ⟨{
    steps := clearAndEmitInvalidSteps input output rows inputCount gateCount
      operand saved outputIndex
    evals_in_steps := clearAndEmitInvalid_phase state input output rows
      inputCount gateCount operand saved outputIndex
    steps_le_m := le_rfl }⟩

/-- Prepend one exact transition to a bounded rejecting suffix. -/
theorem RejectsIn.before_step {start next : machine.Cfg} {rejectBound : Nat}
    (hstep : step start = some next) (hreject : RejectsIn next rejectBound) :
    RejectsIn start (rejectBound + 1) := by
  rcases hreject with ⟨hreject⟩
  have hprefix : EvalsToInTime step start (some next) 1 :=
    { steps := 1, evals_in_steps := hstep, steps_le_m := le_rfl }
  exact ⟨EvalsToInTime.trans step 1 rejectBound start next
    (some (haltList machine [.invalidMark])) hprefix hreject⟩

/-- Prepend an exact multi-step phase to a bounded rejecting suffix. -/
theorem RejectsIn.before_steps {start next : machine.Cfg}
    (phaseSteps : Nat) {rejectBound : Nat}
    (hrun : transition^[phaseSteps] (some start) = some next)
    (hreject : RejectsIn next rejectBound) :
    RejectsIn start (rejectBound + phaseSteps) := by
  rcases hreject with ⟨hreject⟩
  have hprefix : EvalsToInTime step start (some next) phaseSteps :=
    { steps := phaseSteps, evals_in_steps := hrun, steps_le_m := le_rfl }
  exact ⟨EvalsToInTime.trans step phaseSteps rejectBound start next
    (some (haltList machine [.invalidMark])) hprefix hreject⟩

/-- Weaken a local bound to any larger envelope. -/
theorem RejectsIn.mono {start : machine.Cfg} {small large : Nat}
    (hrun : RejectsIn start small) (hbound : small ≤ large) :
    RejectsIn start large := by
  rcases hrun with ⟨hrun⟩
  exact ⟨{ hrun with steps_le_m := hrun.steps_le_m.trans hbound }⟩

/-- A transition directly into cleanup rejects in cleanup cost plus one. -/
theorem rejectsInAfterCleanupStep {start : machine.Cfg} (state : State)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat)
    (hstep : step start = some (cfg (some .clearInput) state input output rows
      inputCount gateCount operand saved outputIndex)) :
    RejectsIn start
      (clearAndEmitInvalidSteps input output rows inputCount gateCount operand
        saved outputIndex + 1) :=
  RejectsIn.before_step hstep
    (cleanup_rejectsIn state input output rows inputCount gateCount operand
      saved outputIndex)

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer


