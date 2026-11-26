-- Prove2me | Definitions.Def_Malliavin_BrownianWickPurePowerComparison
-- name    : Malliavin_BrownianWickPurePowerComparison
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:09:20.401891+00:00
-- url     : https://prove2.me/theorems/e55c891a-e603-570f-8e42-f637f5d3a49e
-- title:
--   Brownian Wick Pure Power Comparison
-- statement:
--   Definitions and structural lemmas for Brownian Wick Pure Power Comparison, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickPurePowerComparison.lean

import Definitions.Def_Malliavin_BrownianWickIsometry
import Definitions.Def_Malliavin_BrownianPurePowerRecurrence
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
def BrownianWickPurePowerMixedInnerIdentity
    (hB : IsPreBrownianReal B P) : Prop :=
  ∀ v n,
    inner ℝ (brownianWickPowerLp hB v n)
        (brownianPurePowerIntegral hB n (stepToLp v)) =
      (n.factorial : ℝ) * (‖stepToLp v‖ ^ 2) ^ n
def BrownianHigherWickPurePowerMixedInnerIdentity
    (hB : IsPreBrownianReal B P) : Prop :=
  ∀ v n, 2 ≤ n →
    inner ℝ (brownianWickPowerLp hB v n)
        (brownianPurePowerIntegral hB n (stepToLp v)) =
      (n.factorial : ℝ) * (‖stepToLp v‖ ^ 2) ^ n
end Malliavin.BrownianIteratedConstruction


