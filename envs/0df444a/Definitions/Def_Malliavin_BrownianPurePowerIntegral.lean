-- Prove2me | Definitions.Def_Malliavin_BrownianPurePowerIntegral
-- name    : Malliavin_BrownianPurePowerIntegral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:06:32.789361+00:00
-- url     : https://prove2.me/theorems/0aa88de3-a53f-5402-8af4-b3c2b60f1037
-- title:
--   Brownian Pure Power Integral
-- statement:
--   Definitions and structural lemmas for Brownian Pure Power Integral, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerIntegral.lean

import Definitions.Def_Malliavin_IteratedKernelPurePower
import Definitions.Def_Malliavin_BrownianPolynomialHermite
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
noncomputable def brownianPurePowerIntegral (hB : IsPreBrownianReal B P)
    (n : ℕ) (f : Lp ℝ 2 nonnegativeLebesgueMeasure) : RandomL2 P :=
  brownianMultipleIntegralCLM hB n (iteratedKernelPurePower n f)
end Malliavin.BrownianIteratedConstruction


