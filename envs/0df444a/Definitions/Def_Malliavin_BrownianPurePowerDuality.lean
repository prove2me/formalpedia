-- Prove2me | Definitions.Def_Malliavin_BrownianPurePowerDuality
-- name    : Malliavin_BrownianPurePowerDuality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:10:26.808471+00:00
-- url     : https://prove2.me/theorems/4b33e4ac-7aac-5027-ad54-e15134389dce
-- title:
--   Brownian Pure Power Duality
-- statement:
--   Definitions and structural lemmas for Brownian Pure Power Duality, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerDuality.lean

import Definitions.Def_Malliavin_BrownianWickPurePowerComparison
import Definitions.Def_Malliavin_BrownianMultipleIntegralBoxSpan
import Definitions.Def_Malliavin_PastCylinderDensity
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
noncomputable def brownianStepDual (coordinate : ℝ≥0 → StrongDual ℝ W)
    (v : ℝ≥0 →₀ ℝ) : StrongDual ℝ W :=
  v.sum fun t c ↦ c • coordinate t
end Malliavin.BrownianIteratedConstruction


