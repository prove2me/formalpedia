-- Prove2me | Definitions.Def_Malliavin_BrownianMultipleIntegral
-- name    : Malliavin_BrownianMultipleIntegral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:01:34.583795+00:00
-- url     : https://prove2.me/theorems/bba3c11b-2673-5c3e-8451-6c27785fe124
-- title:
--   Brownian Multiple Integral
-- statement:
--   Definitions and structural lemmas for Brownian Multiple Integral, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegral.lean

import Definitions.Def_Malliavin_BrownianChaosHilbertSum
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
namespace Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W] in
/-- The canonical Brownian multiple-integral operator
`Iₙ = n! Jₙ ∘ symmetrizeL`. -/
noncomputable def brownianMultipleIntegralCLM
    (hB : IsPreBrownianReal B P) (n : ℕ) :
    IteratedKernel n →L[ℝ] RandomL2 P :=
  (n.factorial : ℝ) • (integralCLM hB n).comp
    (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2)
noncomputable def brownianSymmetricMultipleIntegralRange
    (hB : IsPreBrownianReal B P) (n : ℕ) : Submodule ℝ (RandomL2 P) :=
  LinearMap.range (brownianMultipleIntegralCLM hB n).toLinearMap
end Malliavin.BrownianIteratedConstruction


