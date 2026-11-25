-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineOpenBiInfOfLe
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineOpenBiInfOfLe
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T15:50:47.466487+00:00
-- url     : https://prove2.me/theorems/d0b9a152-490d-418c-b3f3-a1cd5d7bf956
-- title:
--   Is Affine Open Bi Inf Of Le
-- statement:
--   Definitions and structural lemmas for Is Affine Open Bi Inf Of Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsAffineOpenBiInfOfLe.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AcyclicSliceSecCubeOfIsAffineOpen
import Theorems.Thm_GlobalTheory_AbLaw_SecOnR_restrict_bijective
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_restrict_bijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
noncomputable section
namespace GlobalTheory.AbLaw
section
variable {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R)) {M : LB Y}
  {ν κ : Type}
variable (M) in

def comapSecCubeIso (E : ν → Y.Opens) (D : κ → Y.Opens) (g : Finset κ → Finset ν) (hg : Monotone g)
    (h : ∀ t, ⨅ i ∈ g t, E i = ⨅ k ∈ t, D k) :
    Cube.comap g hg (secCube f M E) ≅ secCube f M D :=
  Cube.isoMk (fun t => LinearEquiv.ofBijective (SecOnR.restrict f M (h t).ge)
      (SecOnR.restrict_bijective f (h t).ge (h t).le))
    fun hst x => (SecOnR.restrict_restrict f (iInf_le_iInf_of_subset E (hg hst)) (h _).ge x).trans
      (SecOnR.restrict_restrict f (h _).ge (iInf_le_iInf_of_subset D hst) x).symm
end
end GlobalTheory.AbLaw


