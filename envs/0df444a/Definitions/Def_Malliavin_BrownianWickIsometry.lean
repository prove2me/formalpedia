-- Prove2me | Definitions.Def_Malliavin_BrownianWickIsometry
-- name    : Malliavin_BrownianWickIsometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:04:23.915219+00:00
-- url     : https://prove2.me/theorems/ac878fd7-45bb-5b45-8ccd-d7c464dd63e7
-- title:
--   Brownian Wick Isometry
-- statement:
--   Definitions and structural lemmas for Brownian Wick Isometry, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickIsometry.lean

import Definitions.Def_Malliavin_GaussianHermite
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
end Malliavin.BrownianIteratedConstruction


