-- Prove2me | Definitions.Def_Malliavin_BrownianMultipleIntegralBox
-- name    : Malliavin_BrownianMultipleIntegralBox
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:02:29.553802+00:00
-- url     : https://prove2.me/theorems/1112cc90-8668-593e-a62d-5acdc6c1d896
-- title:
--   Brownian Multiple Integral Box
-- statement:
--   Definitions and structural lemmas for Brownian Multiple Integral Box, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegralBox.lean

import Definitions.Def_Malliavin_BrownianMultipleIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
namespace Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
end Malliavin.BrownianIteratedConstruction


