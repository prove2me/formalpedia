-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupProper
-- name    : Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupProper
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:14:34.101613+00:00
-- url     : https://prove2.me/theorems/9f9fef35-c42d-4d4e-bd76-e54d01637042
-- title:
--   Affine Blowup Proper
-- statement:
--   Definitions and structural lemmas for Affine Blowup Proper, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupProper.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Theorems.Thm_FunctorialResolution_Blowup_AffineBlowup_toSpec_eq_toSpecZero_comp
import Theorems.Thm_FunctorialResolution_Blowup_reesDegreeZeroEquiv_coe_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
namespace FunctorialResolution.Blowup
universe u
variable {R : Type u} [CommRing R]
theorem algebraMap_degreeZero_apply (I : Ideal R) (x : ↥(reesGrading I 0)) :
    algebraMap ↥(reesGrading I 0) ↥(reesAlgebra I) x = (x : ↥(reesAlgebra I)) := rfl
theorem algebraMap_reesAlgebra_eq_algebraMap_degreeZero (I : Ideal R) (r : R) :
    algebraMap R ↥(reesAlgebra I) r =
      algebraMap ↥(reesGrading I 0) ↥(reesAlgebra I) (reesDegreeZeroEquiv I r) := by
  apply Subtype.ext
  rw [algebraMap_degreeZero_apply, reesDegreeZeroEquiv_coe_coe]
  rfl
noncomputable def adjoinOverDegreeZero (I : Ideal R) (s : Set ↥(reesAlgebra I)) :
    Subalgebra R ↥(reesAlgebra I) where
  toSubsemiring := (Algebra.adjoin ↥(reesGrading I 0) s).toSubsemiring
  algebraMap_mem' := fun r => by
    rw [algebraMap_reesAlgebra_eq_algebraMap_degreeZero]
    exact Subalgebra.algebraMap_mem (Algebra.adjoin ↥(reesGrading I 0) s) _
theorem mem_adjoin_degreeZero_of_mem_restrictScalars (I : Ideal R) (s : Set ↥(reesAlgebra I))
    (x : ↥(reesAlgebra I)) (hx : x ∈ adjoinOverDegreeZero I s) :
    x ∈ Algebra.adjoin ↥(reesGrading I 0) s := hx
theorem mem_restrictScalars_of_mem_adjoin_degreeZero (I : Ideal R) (s : Set ↥(reesAlgebra I))
    (x : ↥(reesAlgebra I)) (hx : x ∈ Algebra.adjoin ↥(reesGrading I 0) s) :
    x ∈ adjoinOverDegreeZero I s := hx
theorem adjoin_le_adjoin_degreeZero (I : Ideal R) (s : Set ↥(reesAlgebra I)) :
    Algebra.adjoin R s ≤ adjoinOverDegreeZero I s := by
  refine Algebra.adjoin_le ?_
  intro y hy
  rw [SetLike.mem_coe]
  exact mem_restrictScalars_of_mem_adjoin_degreeZero I s y (Algebra.subset_adjoin hy)
theorem adjoin_degreeZero_eq_top_of_adjoin_eq_top (I : Ideal R) (s : Set ↥(reesAlgebra I))
    (hs : Algebra.adjoin R s = ⊤) : Algebra.adjoin ↥(reesGrading I 0) s = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Algebra.adjoin R s := by
    rw [hs]
    exact Algebra.mem_top
  exact mem_adjoin_degreeZero_of_mem_restrictScalars I s x (adjoin_le_adjoin_degreeZero I s hx)
theorem finiteType_reesAlgebra_degreeZero (I : Ideal R) [IsNoetherianRing R] :
    Algebra.FiniteType ↥(reesGrading I 0) ↥(reesAlgebra I) := by
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType R ↥(reesAlgebra I)).out
  exact ⟨⟨s, adjoin_degreeZero_eq_top_of_adjoin_eq_top I (↑s : Set ↥(reesAlgebra I)) hs⟩⟩
instance instFiniteTypeReesAlgebraOverDegZero (I : Ideal R) [IsNoetherianRing R] :
    Algebra.FiniteType ↥(reesGrading I 0) ↥(reesAlgebra I) :=
  finiteType_reesAlgebra_degreeZero I
theorem isProper_comp_of_isIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : AlgebraicGeometry.IsProper f) (hg : IsIso g) :
    AlgebraicGeometry.IsProper (f ≫ g) := by
  have := hf
  have := hg
  infer_instance
theorem isProper_affineBlowup_toSpec (I : Ideal R) [IsNoetherianRing R] :
    AlgebraicGeometry.IsProper (AffineBlowup.toSpec I) := by
  have hft : Algebra.FiniteType ↥(reesGrading I 0) ↥(reesAlgebra I) :=
    finiteType_reesAlgebra_degreeZero I
  have h1 : AlgebraicGeometry.IsProper (AlgebraicGeometry.Proj.toSpecZero (reesGrading I)) :=
    inferInstance
  rw [AffineBlowup.toSpec_eq_toSpecZero_comp]
  exact isProper_comp_of_isIso _ _ h1 (isIso_SpecMap_iff.mpr (reesDegreeZeroEquiv I).bijective)
instance instIsProperAffineBlowupToSpec (I : Ideal R) [IsNoetherianRing R] :
    AlgebraicGeometry.IsProper (AffineBlowup.toSpec I) :=
  isProper_affineBlowup_toSpec I
theorem locallyOfFiniteType_affineBlowup_toSpec (I : Ideal R) [IsNoetherianRing R] :
    AlgebraicGeometry.LocallyOfFiniteType (AffineBlowup.toSpec I) := by
  have := isProper_affineBlowup_toSpec I
  infer_instance
instance instLocallyOfFiniteTypeAffineBlowupToSpec (I : Ideal R) [IsNoetherianRing R] :
    AlgebraicGeometry.LocallyOfFiniteType (AffineBlowup.toSpec I) :=
  locallyOfFiniteType_affineBlowup_toSpec I
theorem universallyClosed_affineBlowup_toSpec (I : Ideal R) [IsNoetherianRing R] :
    AlgebraicGeometry.UniversallyClosed (AffineBlowup.toSpec I) := by
  have := isProper_affineBlowup_toSpec I
  infer_instance
instance instUniversallyClosedAffineBlowupToSpec (I : Ideal R) [IsNoetherianRing R] :
    AlgebraicGeometry.UniversallyClosed (AffineBlowup.toSpec I) :=
  universallyClosed_affineBlowup_toSpec I
theorem quasiCompact_affineBlowup_toSpec (I : Ideal R) [IsNoetherianRing R] :
    AlgebraicGeometry.QuasiCompact (AffineBlowup.toSpec I) := by
  have := isProper_affineBlowup_toSpec I
  infer_instance
instance instQuasiCompactAffineBlowupToSpec (I : Ideal R) [IsNoetherianRing R] :
    AlgebraicGeometry.QuasiCompact (AffineBlowup.toSpec I) :=
  quasiCompact_affineBlowup_toSpec I
end FunctorialResolution.Blowup


