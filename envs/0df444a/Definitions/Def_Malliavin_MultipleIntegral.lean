-- Prove2me | Definitions.Def_Malliavin_MultipleIntegral
-- name    : Malliavin_MultipleIntegral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:48:46.671563+00:00
-- url     : https://prove2.me/theorems/8c4a18c1-bb37-4d88-8702-26865a9dc208
-- title:
--   Multiple Integral
-- statement:
--   Definitions and structural lemmas for Multiple Integral, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean

import Definitions.Def_Malliavin_IteratedIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
namespace Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}
noncomputable def multipleIntegralCLM (hB : IsPreBrownianReal B P) (n : ℕ) :
    IteratedKernel n →L[ℝ] RandomL2 P :=
  (n.factorial : ℝ) • (iteratedIntegralCLM hB n).comp
    (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2)
end Malliavin
end


