-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_BdRSeries
-- name    : GroundTheory_PAdicHodge_BdRSeries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:17.137835+00:00
-- url     : https://prove2.me/theorems/ae2088d0-103f-4242-921a-97bfa3c69833
-- title:
--   Bd RSeries
-- statement:
--   Definitions and structural lemmas for Bd RSeries, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
open PowerSeries
section TruncEval
variable {S : Type*} [CommRing S] [Algebra ℚ S]
theorem aeval_trunc_coe_of_pow_eq_zero {n : ℕ} {s : S} (hs : s ^ n = 0) (P : Polynomial ℚ) :
    Polynomial.aeval s (trunc n (P : ℚ⟦X⟧)) = Polynomial.aeval s P := by
  have hdvd : Polynomial.X ^ n ∣ P - trunc n (P : ℚ⟦X⟧) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.coeff_sub, coeff_trunc, if_pos hd, Polynomial.coeff_coe, sub_self]
  obtain ⟨Q, hQ⟩ := hdvd
  have h := congrArg (Polynomial.aeval s) hQ
  rw [map_sub, map_mul, map_pow, Polynomial.aeval_X, hs, zero_mul, sub_eq_zero] at h
  exact h.symm
def truncEval {n : ℕ} (s : S) (hs : s ^ n = 0) : ℚ⟦X⟧ →ₐ[ℚ] S where
  toFun f := Polynomial.aeval s (trunc n f)
  map_one' := by
    rcases n with _ | n
    · have : Subsingleton S := subsingleton_of_zero_eq_one (by simpa using hs.symm)
      exact Subsingleton.elim _ _
    · rw [← Polynomial.coe_one, aeval_trunc_coe_of_pow_eq_zero hs, map_one]
  map_mul' f g := by
    rw [← trunc_trunc_mul_trunc, ← Polynomial.coe_mul, aeval_trunc_coe_of_pow_eq_zero hs, map_mul]
  map_zero' := by
    rw [map_zero, map_zero]
  map_add' f g := by
    rw [map_add, map_add]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul, ← Polynomial.coe_one,
      aeval_trunc_coe_of_pow_eq_zero hs, map_one, ← Algebra.algebraMap_eq_smul_one]
theorem truncEval_apply {n : ℕ} (s : S) (hs : s ^ n = 0) (f : ℚ⟦X⟧) :
    truncEval s hs f = Polynomial.aeval s (trunc n f) := rfl
theorem truncEval_eq_sum {n : ℕ} (s : S) (hs : s ^ n = 0) (f : ℚ⟦X⟧) :
    truncEval s hs f = ∑ i ∈ Finset.range n, algebraMap ℚ S (coeff i f) * s ^ i := by
  rcases n with _ | n
  · have : Subsingleton S := subsingleton_of_zero_eq_one (by simpa using hs.symm)
    exact Subsingleton.elim _ _
  · rw [truncEval_apply, Polynomial.aeval_eq_sum_range' (natDegree_trunc_lt f n)]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [coeff_trunc, if_pos (Finset.mem_range.1 hi), Algebra.smul_def]
@[simp]
theorem truncEval_X {n : ℕ} (s : S) (hs : s ^ n = 0) : truncEval s hs X = s := by
  rcases n with _ | _ | n
  · have : Subsingleton S := subsingleton_of_zero_eq_one (by simpa using hs.symm)
    exact Subsingleton.elim _ _
  · rw [pow_one] at hs
    rw [truncEval_eq_sum, Finset.sum_range_one, coeff_zero_X, map_zero, zero_mul, hs]
  · rw [truncEval_apply, trunc_X, Polynomial.aeval_X]
theorem truncEval_unique {n : ℕ} (ψ : ℚ⟦X⟧ →ₐ[ℚ] S) (s : S) (hs : s ^ n = 0) (hψ : ψ X = s) :
    ψ = truncEval s hs := by
  have hpoly : (ψ.comp (Polynomial.coeToPowerSeries.algHom ℚ)) = Polynomial.aeval s := by
    apply Polynomial.algHom_ext
    simp [hψ]
  ext f
  obtain ⟨h, hh⟩ : X ^ n ∣ f - (trunc n f : ℚ⟦X⟧) := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, Polynomial.coeff_coe, coeff_trunc, if_pos hm, sub_self]
  have h1 : ψ f = ψ (trunc n f : ℚ⟦X⟧) := by
    have := congrArg ψ hh
    rw [map_sub, map_mul, map_pow, hψ, hs, zero_mul, sub_eq_zero] at this
    exact this
  rw [h1, truncEval_apply]
  exact congrArg (fun F : Polynomial ℚ →ₐ[ℚ] S => F (trunc n f)) hpoly
end TruncEval
section SeriesEval
variable {B : Type*} [CommRing B] (I : Ideal B)
theorem pow_mk_eq_zero {z : B} (hz : z ∈ I) (n : ℕ) :
    (Ideal.Quotient.mk (I ^ n) z) ^ n = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow hz n
variable [Algebra ℚ B]
theorem factorₐ_comp_truncEval {z : B} (hz : z ∈ I) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ ℚ (Ideal.pow_le_pow_right hle)).comp
        (truncEval (Ideal.Quotient.mk (I ^ n) z) (pow_mk_eq_zero I hz n)) =
      truncEval (Ideal.Quotient.mk (I ^ m) z) (pow_mk_eq_zero I hz m) := by
  apply truncEval_unique
  rw [AlgHom.comp_apply, truncEval_X]
  rfl
variable [IsAdicComplete I B]
def seriesEval (z : B) (hz : z ∈ I) : ℚ⟦X⟧ →ₐ[ℚ] B :=
  IsAdicComplete.liftAlgHom I
    (fun n => truncEval (Ideal.Quotient.mk (I ^ n) z) (pow_mk_eq_zero I hz n))
    (fun hle => factorₐ_comp_truncEval I hz hle)
variable {I}
end SeriesEval
section Log
variable {B : Type*} [CommRing B] [Algebra ℚ B] {I : Ideal B} [IsAdicComplete I B]
variable (I) in

def logOnePlus (z : B) (hz : z ∈ I) : B :=
  seriesEval I z hz (log ℚ)
end Log
end GroundTheory.PAdicHodge


