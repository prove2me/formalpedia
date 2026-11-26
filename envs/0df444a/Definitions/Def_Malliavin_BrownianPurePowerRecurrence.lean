-- Prove2me | Definitions.Def_Malliavin_BrownianPurePowerRecurrence
-- name    : Malliavin_BrownianPurePowerRecurrence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:08:36.494433+00:00
-- url     : https://prove2.me/theorems/9c309bc9-5a9b-4bfa-9f59-7bbe2029db43
-- title:
--   Brownian Pure Power Recurrence
-- statement:
--   Definitions and structural lemmas for Brownian Pure Power Recurrence, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerRecurrence.lean

import Definitions.Def_Malliavin_BrownianHermiteMultipleIntegral
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
noncomputable def brownianStepTimesWickPowerLp
    (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) (n : ℕ) : RandomL2 P :=
  polynomialFamilyLinearMap (brownianStepPowerLp hB v)
    (Polynomial.X * varianceHermite (‖stepToLp v‖ ^ 2) n)
def BrownianPurePowerHermiteRecurrence (hB : IsPreBrownianReal B P) : Prop :=
  ∀ v n,
    brownianPurePowerIntegral hB (n + 2) (stepToLp v) =
      brownianStepTimesWickPowerLp hB v (n + 1) -
        (‖stepToLp v‖ ^ 2 * ((n + 1 : ℕ) : ℝ)) •
          brownianPurePowerIntegral hB n (stepToLp v)
end Malliavin.BrownianIteratedConstruction


