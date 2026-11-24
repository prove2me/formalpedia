-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCoverModelIrreducibleSpecialFibre
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCoverModelIrreducibleSpecialFibre
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T19:15:30.174204+00:00
-- url     : https://prove2.me/theorems/9b2a6f06-9225-495c-a796-b20a5f420dd9
-- title:
--   Exists Cover Model Irreducible Special Fibre
-- statement:
--   Definitions and structural lemmas for Exists Cover Model Irreducible Special Fibre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsCoverModelIrreducibleSpecialFibre.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.IrrSplit
section
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}
theorem isPullback_lift (M : Model R A) (U : M.Y.left.Opens)
    (hU : Set.range (pullback.fst M.Y.hom (spMap (algebraMap R K))) ⊆ Set.range U.ι) :
    IsPullback (IsOpenImmersion.lift U.ι (pullback.fst M.Y.hom (spMap (algebraMap R K))) hU)
      (pullback.snd M.Y.hom (spMap (algebraMap R K))) (U.ι ≫ M.Y.hom) (spMap (algebraMap R K)) := by
  refine ⟨⟨by rw [IsOpenImmersion.lift_fac_assoc, pullback.condition]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c => pullback.lift (c.fst ≫ U.ι) c.snd (by simpa using c.condition)) ?_ ?_ ?_⟩⟩
  · intro c
    rw [← cancel_mono U.ι, Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  · intro c
    rw [pullback.lift_snd]
  · intro c m h₁ h₂
    apply pullback.hom_ext
    · rw [pullback.lift_fst, ← h₁, Category.assoc, IsOpenImmersion.lift_fac]
    · rw [pullback.lift_snd, h₂]
def restrictModel (M : Model R A) (U : M.Y.left.Opens) [QuasiCompact U.ι]
    (hU : Set.range (pullback.fst M.Y.hom (spMap (algebraMap R K))) ⊆ Set.range U.ι) : Model R A where
  Y := Over.mk (U.ι ≫ M.Y.hom)
  e := Over.isoMk (g := (Over.pullback (spMap (algebraMap R K))).obj M.Y) (isPullback_lift M U hU).isoPullback.symm
    ((isPullback_lift M U hU).isoPullback_inv_snd) ≪≫ M.e
  smooth := by have := M.smooth; show Smooth (U.ι ≫ M.Y.hom); infer_instance
  sep := by have := M.sep; show IsSeparated (U.ι ≫ M.Y.hom); infer_instance
  qc := by have := M.qc; show QuasiCompact (U.ι ≫ M.Y.hom); infer_instance
end
end GlobalTheory.SS.IrrSplit
end


