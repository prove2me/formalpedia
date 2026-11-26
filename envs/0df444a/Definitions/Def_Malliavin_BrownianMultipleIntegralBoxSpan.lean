-- Prove2me | Definitions.Def_Malliavin_BrownianMultipleIntegralBoxSpan
-- name    : Malliavin_BrownianMultipleIntegralBoxSpan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:03:23.382211+00:00
-- url     : https://prove2.me/theorems/cd436379-386c-5187-b419-59d4f299c532
-- title:
--   Brownian Multiple Integral Box Span
-- statement:
--   Definitions and structural lemmas for Brownian Multiple Integral Box Span, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegralBoxSpan.lean

import Definitions.Def_Malliavin_BrownianMultipleIntegralBox
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
namespace Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Formal finite combinations of ordered-box indicators in full product `L²`. -/
noncomputable def orderedBoxToIteratedKernel (n : ℕ) :
    (OrderedBoxIndex n →₀ ℝ) →ₗ[ℝ] IteratedKernel n :=
  Finsupp.linearCombination ℝ fun a ↦ boxKernel a.u a.v
omit [CompleteSpace W] [BorelSpace W] in
/-- The canonical multiple-integral operator restricted to formal finite ordered-box
combinations. -/
noncomputable def canonicalOrderedBoxMultipleIntegralMap
    (hB : IsPreBrownianReal B P) (n : ℕ) :
    (OrderedBoxIndex n →₀ ℝ) →ₗ[ℝ] RandomL2 P :=
  (brownianMultipleIntegralCLM hB n).toLinearMap.comp (orderedBoxToIteratedKernel n)
omit [CompleteSpace W] [BorelSpace W] in
/-- The algebraic range of finite ordered Brownian increment chains of one fixed order. -/
noncomputable def brownianOrderedBoxOrderRange
    (hB : IsPreBrownianReal B P) (n : ℕ) : Submodule ℝ (RandomL2 P) :=
  LinearMap.range (orderedBoxToRandom hB n)
end Malliavin.BrownianIteratedConstruction


