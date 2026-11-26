-- Prove2me | Definitions.Def_Malliavin_BrownianClarkOconeCapstone
-- name    : Malliavin_BrownianClarkOconeCapstone
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:47:43.553426+00:00
-- url     : https://prove2.me/theorems/e221e774-f087-4884-a142-af31abcb316f
-- title:
--   Brownian Clark Ocone Capstone
-- statement:
--   Definitions and structural lemmas for Brownian Clark Ocone Capstone, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianClarkOconeCapstone.lean

import Definitions.Def_Malliavin_BrownianHermiteClarkOcone
import Definitions.Def_Malliavin_BrownianPurePowerDuality
import Definitions.Def_Malliavin_ClarkOconeExamples
import Definitions.Def_Malliavin_NaturalFiltrationLeftContinuous
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_higherHermiteMultipleIntegralIdentity_of_generated

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
namespace Malliavin
open BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
noncomputable def ClarkOconeFamily.ofGenerated
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm) :
    ClarkOconeFamily B P filtration :=
  ClarkOconeFamily.ofHermiteMultipleIntegralIdentity
    hB coordinate coordinate_apply generated hsm hnat
    (higherHermiteMultipleIntegralIdentity_of_generated
      hB coordinate coordinate_apply generated hsm)
end Malliavin


