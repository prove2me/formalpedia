-- Prove2me | Definitions.Def_PricingWithTips3DM_21a2610e894ac9752435705f
-- name    : PricingWithTips3DM_21a2610e894ac9752435705f
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T21:16:26.171392+00:00
-- url     : https://prove2.me/theorems/d19c482f-7ac8-457e-9d8f-a9b78a3b1988
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Normalizer.Run
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_2734e67172f2de8a3b6e575e
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Guarded circuit normalizer: public exact run

This small facade packages total exact semantics in Mathlib's standard
`TM2OutputsInTime` interface.  The time parameter is the chosen exact run
length; the next layer replaces it with one uniform polynomial in input size.
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

open Computability StateTransition

/-- The fixed normalizer outputs the guarded normalization on every raw input
in some finite number of steps. -/
theorem outputs (input : List CircuitSym) :
    ∃ steps,
      Nonempty (_root_.Turing.TM2OutputsInTime machine input
        (some (normalizeGeneralCircuit input)) steps) := by
  rcases normalizer_run input with ⟨steps, hrun⟩
  refine ⟨steps, ⟨{
    steps := steps
    evals_in_steps := ?_
    steps_le_m := le_rfl }⟩⟩
  change (flip Option.bind step)^[steps]
    (some (_root_.Turing.initList machine input)) =
      some (_root_.Turing.haltList machine (normalizeGeneralCircuit input))
  exact hrun

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer


