-- Prove2me | Definitions.Def_Malliavin_BrownianHermiteClarkOcone
-- name    : Malliavin_BrownianHermiteClarkOcone
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:44:59.953723+00:00
-- url     : https://prove2.me/theorems/7d3d4786-908e-48da-98b8-9eb2ce3501ab
-- title:
--   Brownian Hermite Clark Ocone
-- statement:
--   Definitions and structural lemmas for Brownian Hermite Clark Ocone, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermiteClarkOcone.lean

import Definitions.Def_Malliavin_BrownianHermiteMultipleIntegral
import Definitions.Def_Malliavin_PastCylinderDensity
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_naturalMartingaleRepresentation_of_hermiteMultipleIntegralIdentity
import Theorems.Thm_Malliavin_naturalItoDuality_natural

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
noncomputable def ClarkOconeFamily.ofHermiteMultipleIntegralIdentity
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm)
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB) :
    ClarkOconeFamily B P filtration := by
  exact ClarkOconeFamily.ofNaturalIto
    hB coordinate coordinate_apply generated hsm hnat
    (naturalMartingaleRepresentation_of_hermiteMultipleIntegralIdentity
      hB hsm hnat generated hid)
    (fun F U ↦ naturalItoDuality_natural
      hB coordinate coordinate_apply generated hsm hnat F U)
end Malliavin


