-- Prove2me | Definitions.Def_Malliavin_BrownianHermiteMultipleIntegral
-- name    : Malliavin_BrownianHermiteMultipleIntegral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:07:28.916853+00:00
-- url     : https://prove2.me/theorems/848d19a9-59ed-586c-9652-f66876f083cb
-- title:
--   Brownian Hermite Multiple Integral
-- statement:
--   Definitions and structural lemmas for Brownian Hermite Multiple Integral, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermiteMultipleIntegral.lean

import Definitions.Def_Malliavin_BrownianPurePowerIntegral
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
def BrownianHigherHermiteMultipleIntegralIdentity
    (hB : IsPreBrownianReal B P) : Prop :=
  ∀ v n, 2 ≤ n →
    brownianWickPowerLp hB v n =
      brownianPurePowerIntegral hB n (stepToLp v)
end Malliavin.BrownianIteratedConstruction


