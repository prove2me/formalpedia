-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveSpaceChart
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveSpaceChart
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T18:56:08.002388+00:00
-- url     : https://prove2.me/theorems/740e6dd7-5fdf-4a89-81fa-9c5bfb710c51
-- title:
--   Projective Space Chart
-- statement:
--   Definitions and structural lemmas for Projective Space Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveSpaceChart.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
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
open AlgebraicGeometry MvPolynomial HomogeneousLocalization
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
namespace ProjSpace
variable (A : Type u) [CommRing A] {n : ℕ} (i : Fin (n + 1))
abbrev Chart := Away (grading A n) (X i : MvPolynomial (Fin (n + 1)) A)
abbrev ChartLoc := Localization.Away (X i : MvPolynomial (Fin (n + 1)) A)
def dehom : MvPolynomial (Fin (n + 1)) A →+* MvPolynomial {j // j ≠ i} A :=
  eval₂Hom C (fun j => if h : j = i then 1 else X ⟨j, h⟩)
lemma dehom_X_self : dehom A i (X i) = 1 := by simp [dehom]
lemma dehom_X_of_ne (j : Fin (n + 1)) (h : j ≠ i) : dehom A i (X j) = X ⟨j, h⟩ := by
  simp [dehom, h]
lemma dehom_C (a : A) : dehom A i (C a) = C a := by simp [dehom]
def chartToPoly : Chart A i →+* MvPolynomial {j // j ≠ i} A :=
  (Localization.awayLift (dehom A i) (X i) (by rw [dehom_X_self]; exact isUnit_one)).comp
    (algebraMap (Chart A i) (ChartLoc A i))
def coordinate (j : {j // j ≠ i}) : Chart A i :=
  Away.mk (grading A n) (X_mem i) 1 (X j.1) (by simpa using X_mem (A := A) j.1)
def polyToChart : MvPolynomial {j // j ≠ i} A →+* Chart A i :=
  eval₂Hom ((fromZeroRingHom (grading A n) _).comp (algebraMap A (grading A n 0)))
    (coordinate A i)
def scaleMap : MvPolynomial (Fin (n + 1)) A →+* ChartLoc A i :=
  eval₂Hom ((algebraMap (MvPolynomial (Fin (n + 1)) A) (ChartLoc A i)).comp C)
    (fun j => algebraMap (MvPolynomial (Fin (n + 1)) A) (ChartLoc A i) (X j) *
      IsLocalization.Away.invSelf (S := ChartLoc A i) (X i : MvPolynomial (Fin (n + 1)) A))
end ProjSpace
namespace ProjSpace
variable (A : Type u) [CommRing A] {n : ℕ} (i : Fin (n + 1))
local notation "Pn" => MvPolynomial (Fin (n + 1)) A
local notation "xinv" => IsLocalization.Away.invSelf (S := ChartLoc A i) (X i : MvPolynomial (Fin (n + 1)) A)
lemma algebraMap_X_mul_invSelf :
    algebraMap (MvPolynomial (Fin (n + 1)) A) (ChartLoc A i) (X i) * xinv = 1 :=
  IsLocalization.Away.mul_invSelf _
lemma val_coordinate (j : {j // j ≠ i}) :
    (coordinate A i j).val = algebraMap Pn (ChartLoc A i) (X j.1) * xinv := by
  rw [coordinate, Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one,
    IsLocalization.Away.invSelf]
  congr 2
  exact Subtype.ext (pow_one _)
lemma val_polyToChart_C (a : A) :
    (polyToChart A i (C a)).val = algebraMap Pn (ChartLoc A i) (C a) := by
  simp [polyToChart, fromZeroRingHom]
  rfl
lemma scaleMap_eq :
    (algebraMap (Chart A i) (ChartLoc A i)).comp ((polyToChart A i).comp (dehom A i)) =
      scaleMap A i := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, dehom_C, HomogeneousLocalization.algebraMap_apply]
    rw [val_polyToChart_C]
    simp [scaleMap]
  · intro j
    simp only [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
    by_cases h : j = i
    · subst h
      rw [dehom_X_self, map_one, val_one]
      simp only [scaleMap, coe_eval₂Hom, eval₂_X]
      exact (algebraMap_X_mul_invSelf A j).symm
    · rw [dehom_X_of_ne A i j h]
      simp only [polyToChart, coe_eval₂Hom, eval₂_X, scaleMap]
      exact val_coordinate A i ⟨j, h⟩
lemma scaleMap_monomial (e : Fin (n + 1) →₀ ℕ) (c : A) :
    scaleMap A i (monomial e c) * algebraMap Pn (ChartLoc A i) (X i ^ e.degree) =
      algebraMap Pn (ChartLoc A i) (monomial e c) := by
  have hdeg : e.degree = ∑ j ∈ e.support, e j := rfl
  have hinv : (e.prod fun _ k => xinv ^ k) * algebraMap Pn (ChartLoc A i) (X i ^ e.degree) = 1 := by
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, map_pow, ← hdeg, ← mul_pow, mul_comm,
      algebraMap_X_mul_invSelf, one_pow]
  simp only [scaleMap, coe_eval₂Hom, eval₂_monomial, RingHom.comp_apply]
  simp_rw [mul_pow]
  rw [Finsupp.prod_mul, mul_assoc, mul_assoc, hinv, mul_one, monomial_eq, map_mul, map_finsuppProd]
  simp only [map_pow]
lemma scaleMap_homog {m : ℕ} {a : Pn} (ha : a ∈ grading A n m) :
    scaleMap A i a * algebraMap Pn (ChartLoc A i) (X i ^ m) = algebraMap Pn (ChartLoc A i) a := by
  have hh : a.IsHomogeneous m := (mem_homogeneousSubmodule m a).1 ha
  conv_lhs => rw [a.as_sum]
  conv_rhs => rw [a.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun e he => ?_)
  have hdeg : e.degree = m := by
    have := hh (mem_support_iff.mp he)
    rwa [Finsupp.degree_eq_weight_one]
  rw [← hdeg]
  exact scaleMap_monomial A i e _
lemma chartToPoly_mk (m : ℕ) (a : Pn) (ha : a ∈ grading A n (m • 1)) :
    chartToPoly A i (Away.mk (grading A n) (X_mem i) m a ha) = dehom A i a := by
  have := Localization.awayLift_mk (dehom A i) (X i) a 1 (by rw [dehom_X_self, one_mul]) m
  simp only [chartToPoly, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk]
  refine this.trans ?_
  rw [one_pow, mul_one]
lemma chartToPoly_algebraMap (a : Pn) (h) :
    Localization.awayLift (dehom A i) (X i) h (algebraMap Pn (ChartLoc A i) a) = dehom A i a :=
  IsLocalization.Away.lift_eq _ _ a
lemma chartToPoly_polyToChart : (chartToPoly A i).comp (polyToChart A i) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, RingHom.id_apply, chartToPoly,
      HomogeneousLocalization.algebraMap_apply]
    rw [val_polyToChart_C, chartToPoly_algebraMap, dehom_C]
  · intro j
    simp only [RingHom.comp_apply, RingHom.id_apply, polyToChart, coe_eval₂Hom, eval₂_X,
      coordinate]
    rw [chartToPoly_mk, dehom_X_of_ne A i j.1 j.2]
lemma polyToChart_chartToPoly : (polyToChart A i).comp (chartToPoly A i) = RingHom.id _ := by
  ext z : 1
  obtain ⟨m, a, ha, rfl⟩ := Away.mk_surjective (grading A n) (X_mem i) z
  rw [RingHom.comp_apply, chartToPoly_mk, RingHom.id_apply]
  apply HomogeneousLocalization.val_injective
  have h1 := congrArg (fun φ => φ a) (scaleMap_eq A i)
  simp only [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply] at h1
  rw [h1, Away.val_mk, Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq]
  have := scaleMap_homog A i (m := m) (a := a) (by simpa using ha)
  exact this
def chartEquiv : Chart A i ≃+* MvPolynomial {j // j ≠ i} A :=
  RingEquiv.ofRingHom (chartToPoly A i) (polyToChart A i) (chartToPoly_polyToChart A i)
    (polyToChart_chartToPoly A i)
instance [IsDomain A] : IsDomain (Chart A i) :=
  (chartEquiv A i).toMulEquiv.isDomain
instance [IsNoetherianRing A] : IsNoetherianRing (Chart A i) :=
  isNoetherianRing_of_ringEquiv _ (chartEquiv A i).symm
instance {k : Type u} [Field k] : UniqueFactorizationMonoid (Chart k i) :=
  (chartEquiv k i).toMulEquiv.symm.uniqueFactorizationMonoid inferInstance
end ProjSpace
end
end GroundTheory.Arith.SchemeCoh


