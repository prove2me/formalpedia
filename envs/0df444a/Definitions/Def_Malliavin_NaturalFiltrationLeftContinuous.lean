-- Prove2me | Definitions.Def_Malliavin_NaturalFiltrationLeftContinuous
-- name    : Malliavin_NaturalFiltrationLeftContinuous
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:12:15.017595+00:00
-- url     : https://prove2.me/theorems/c4006bad-a400-51bb-9cb2-fda566e88224
-- title:
--   Natural Filtration Left Continuous
-- statement:
--   Definitions and structural lemmas for Natural Filtration Left Continuous, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalFiltrationLeftContinuous.lean

import Definitions.Def_Malliavin_PointwiseCondExp
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
namespace Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
section ClarkOcone
variable {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
end ClarkOcone
end Malliavin


