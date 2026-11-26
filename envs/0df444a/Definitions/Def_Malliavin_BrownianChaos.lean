-- Prove2me | Definitions.Def_Malliavin_BrownianChaos
-- name    : Malliavin_BrownianChaos
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:46:29.554891+00:00
-- url     : https://prove2.me/theorems/2c89c4bc-ccec-4bcd-8a3d-0a2a5391c0f9
-- title:
--   Brownian Chaos
-- statement:
--   Definitions and structural lemmas for Brownian Chaos, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaos.lean

import Definitions.Def_Malliavin_BrownianOrderedBoxDensity
import Definitions.Def_Malliavin_NaturalClarkOcone
import Definitions.Def_Malliavin_NaturalItoRange
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
noncomputable def brownianMultipleIntegralRange
    (hB : IsPreBrownianReal B P) (n : ℕ) : Submodule ℝ (RandomL2 P) :=
  LinearMap.range (integralCLM hB n).toLinearMap
noncomputable def brownianHomogeneousChaos
    (hB : IsPreBrownianReal B P) (n : ℕ) : ClosedSubmodule ℝ (RandomL2 P) :=
  (brownianMultipleIntegralRange hB n).closure
end Malliavin.BrownianIteratedConstruction


