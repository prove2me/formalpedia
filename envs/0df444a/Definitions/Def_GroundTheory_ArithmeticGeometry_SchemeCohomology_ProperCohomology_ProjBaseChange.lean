-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ProjBaseChange
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ProjBaseChange
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T03:55:26.5879+00:00
-- url     : https://prove2.me/theorems/cb17c4ea-e987-4d21-82bc-91c33b018006
-- title:
--   Proj Base Change
-- statement:
--   Definitions and structural lemmas for Proj Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjBaseChange.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveSpaceChart
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_TwistingSheaf
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_X_mem
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_ext
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_add
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_mkSection
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_neg
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_sub
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_add
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_mkSection
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_neg
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_sub
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_zero


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Limits MvPolynomial HomogeneousLocalization
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
namespace ProjSpace
lemma irrelevant_le_span_X (A : Type u) [CommRing A] (n : ℕ) :
    (HomogeneousIdeal.irrelevant (grading A n)).toIdeal ≤
      Ideal.span (Set.range (X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) A)) := by
  intro p hp
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  by_contra! h
  have hm0 : m = 0 := Finsupp.ext fun i => h i (Set.mem_univ i)
  subst hm0
  have h0 : GradedRing.proj (grading A n) 0 p = 0 := hp
  rw [GradedRing.proj_apply] at h0
  change ((MvPolynomial.decomposition.decompose' p 0 : homogeneousSubmodule (Fin (n + 1)) A 0) :
    MvPolynomial (Fin (n + 1)) A) = 0 at h0
  rw [MvPolynomial.decomposition.decompose'_apply, homogeneousComponent_zero, C_eq_zero] at h0
  exact (MvPolynomial.mem_support_iff.mp hm) h0
variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ)
def gradedMap : grading A n →+*ᵍ grading B n where
  toRingHom := MvPolynomial.map (algebraMap A B)
  map_mem {_ _} hx :=
    (mem_homogeneousSubmodule _ _).2 (((mem_homogeneousSubmodule _ _).1 hx).map _)
lemma gradedMap_apply (p : MvPolynomial (Fin (n + 1)) A) :
    gradedMap A B n p = MvPolynomial.map (algebraMap A B) p := rfl
@[simp] lemma gradedMap_X (j : Fin (n + 1)) : gradedMap A B n (X j) = X j := by
  simp [gradedMap_apply]
lemma irrelevant_le_map :
    HomogeneousIdeal.irrelevant (grading B n) ≤
      (HomogeneousIdeal.irrelevant (grading A n)).map (gradedMap A B n) := by
  rw [← toIdeal_le_toIdeal_iff, HomogeneousIdeal.toIdeal_map]
  refine (irrelevant_le_span_X B n).trans (Ideal.span_le.2 ?_)
  rintro _ ⟨j, rfl⟩
  rw [← gradedMap_X A B n j]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos (X_mem j))
def baseChangeMap : projectiveSpace B n ⟶ projectiveSpace A n :=
  Proj.map (gradedMap A B n) (irrelevant_le_map A B n)
def stdAffineCover (A : Type u) [CommRing A] (n : ℕ) : (projectiveSpace A n).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (grading A n)
    (fun j : Fin (n + 1) => (X j : MvPolynomial (Fin (n + 1)) A)) (fun j => X_mem j)
    (fun _ => Nat.one_pos) (irrelevant_le_span_X A n)
def chartAlgebraMap (A : Type u) [CommRing A] {n : ℕ} (s : MvPolynomial (Fin (n + 1)) A) :
    A →+* Away (grading A n) s :=
  (fromZeroRingHom (grading A n) _).comp (algebraMap A (grading A n 0))
def awayCongr {s t : MvPolynomial (Fin (n + 1)) B} (h : s = t) :
    Away (grading B n) s ≃+* Away (grading B n) t := by
  subst h
  exact RingEquiv.refl _
variable {A B n}
end ProjSpace
end
end GroundTheory.Arith.SchemeCoh


