-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
-- name    : Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T12:24:42.206797+00:00
-- url     : https://prove2.me/theorems/8c17b1d2-9946-4578-b380-8f91b6e8aa4b
-- title:
--   Affine Blowup
-- statement:
--   Definitions and structural lemmas for Affine Blowup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowup.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Theorems.Thm_FunctorialResolution_Blowup_reesDegreeZeroEquiv_apply
import Theorems.Thm_FunctorialResolution_Blowup_reesGenerator_mem_reesGrading
import Theorems.Thm_FunctorialResolution_Blowup_reesGrading_irrelevant_le_span
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.Blowup.reesDegreeZeroEquiv_apply


set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
namespace FunctorialResolution.Blowup
universe u
variable {R : Type u} [CommRing R]
noncomputable def affineBlowup (I : Ideal R) : Scheme.{u} :=
  AlgebraicGeometry.Proj (reesGrading I)
namespace AffineBlowup
noncomputable def toSpec (I : Ideal R) :
    affineBlowup I ⟶ AlgebraicGeometry.Spec (CommRingCat.of R) :=
  AlgebraicGeometry.Proj.toSpecZero (reesGrading I) ≫
    AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom
        ((reesDegreeZeroEquiv I : R ≃+* ↥(reesGrading I 0)) : R →+* ↥(reesGrading I 0)))
end AffineBlowup
noncomputable def affineBlowupChart (I : Ideal R) (a : ↥I) :
    AlgebraicGeometry.Spec
        (CommRingCat.of (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a))) ⟶
      affineBlowup I :=
  AlgebraicGeometry.Proj.awayι (reesGrading I) (reesGenerator I a) (reesGenerator_mem_reesGrading I a)
    Nat.one_pos
instance instIsOpenImmersionAffineBlowupChart (I : Ideal R) (a : ↥I) :
    AlgebraicGeometry.IsOpenImmersion (affineBlowupChart I a) :=
  inferInstanceAs (AlgebraicGeometry.IsOpenImmersion
    (AlgebraicGeometry.Proj.awayι (reesGrading I) (reesGenerator I a) (reesGenerator_mem_reesGrading I a)
      Nat.one_pos))
theorem opensRange_affineBlowupChart_eq_basicOpen (I : Ideal R) (a : ↥I) :
    (affineBlowupChart I a).opensRange =
      AlgebraicGeometry.Proj.basicOpen (reesGrading I) (reesGenerator I a) :=
  AlgebraicGeometry.Proj.opensRange_awayι ..
theorem iSup_proj_basicOpen_reesGenerator_eq_top (I : Ideal R) :
    (⨆ a : ↥I, AlgebraicGeometry.Proj.basicOpen (reesGrading I) (reesGenerator I a)) = ⊤ := by
  apply AlgebraicGeometry.Proj.iSup_basicOpen_eq_top
  exact reesGrading_irrelevant_le_span I
theorem exists_mem_range_affineBlowupChart (I : Ideal R) (x : ↥(affineBlowup I)) :
    ∃ a : ↥I, x ∈ Set.range (affineBlowupChart I a).base := by
  have h2 : (⋃ a : ↥I,
      ((AlgebraicGeometry.Proj.basicOpen (reesGrading I) (reesGenerator I a) :
          (AlgebraicGeometry.Proj (reesGrading I)).Opens) :
        Set ↥(AlgebraicGeometry.Proj (reesGrading I)))) = Set.univ := by
    rw [← TopologicalSpace.Opens.coe_iSup, iSup_proj_basicOpen_reesGenerator_eq_top]
    simp
  have hx : x ∈ (⋃ a : ↥I,
      ((AlgebraicGeometry.Proj.basicOpen (reesGrading I) (reesGenerator I a) :
          (AlgebraicGeometry.Proj (reesGrading I)).Opens) :
        Set ↥(AlgebraicGeometry.Proj (reesGrading I)))) := by
    rw [h2]
    exact Set.mem_univ _
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
  refine ⟨a, ?_⟩
  have hs : Set.range (affineBlowupChart I a).base =
      ((AlgebraicGeometry.Proj.basicOpen (reesGrading I) (reesGenerator I a) :
          (AlgebraicGeometry.Proj (reesGrading I)).Opens) :
        Set ↥(AlgebraicGeometry.Proj (reesGrading I))) :=
    congrArg (fun U : (affineBlowup I).Opens => (U : Set ↥(affineBlowup I)))
      (opensRange_affineBlowupChart_eq_basicOpen I a)
  rw [hs]
  exact ha
noncomputable def affineBlowupAffineOpenCover (I : Ideal R) : (affineBlowup I).AffineOpenCover where
  I₀ := ↥I
  X a := CommRingCat.of (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a))
  f a := affineBlowupChart I a
  idx x := (exists_mem_range_affineBlowupChart I x).choose
  covers x := (exists_mem_range_affineBlowupChart I x).choose_spec
  map_prop a := instIsOpenImmersionAffineBlowupChart I a
noncomputable def chartRingHom (I : Ideal R) (a : ↥I) :
    R →+* HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a) :=
  (HomogeneousLocalization.fromZeroRingHom (reesGrading I)
      (Submonoid.powers (reesGenerator I a))).comp
    ((reesDegreeZeroEquiv I : R ≃+* ↥(reesGrading I 0)) : R →+* ↥(reesGrading I 0))
noncomputable instance AffineBlowup.instAlgebraChart (I : Ideal R) (a : ↥I) :
    Algebra R (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) :=
  RingHom.toAlgebra (chartRingHom I a)
theorem reesGenerator_pow_one_mem_reesGrading_one (I : Ideal R) (a : ↥I) :
    reesGenerator I a ^ 1 ∈ reesGrading I 1 := by
  rw [pow_one]
  exact reesGenerator_mem_reesGrading I a
theorem reesGenerator_pow_one_mem_powers (I : Ideal R) (a : ↥I) :
    reesGenerator I a ^ 1 ∈ Submonoid.powers (reesGenerator I a) :=
  Submonoid.pow_mem _ (Submonoid.mem_powers _) 1
noncomputable def chartFraction (I : Ideal R) (a b : ↥I) :
    HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a) :=
  HomogeneousLocalization.mk
    { deg := 1
      num := ⟨reesGenerator I b, reesGenerator_mem_reesGrading I b⟩
      den := ⟨reesGenerator I a ^ 1, reesGenerator_pow_one_mem_reesGrading_one I a⟩
      den_mem := reesGenerator_pow_one_mem_powers I a }
end FunctorialResolution.Blowup


