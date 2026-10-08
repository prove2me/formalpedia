-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13LaurentPolynomialOrder_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13LaurentPolynomialOrder_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:44:47.326203+00:00
-- url     : https://prove2.me/theorems/4c03c164-602d-43c3-99ea-450c5aad473f
-- title:
--   FLT.Assumptions.MazurProof.N13LaurentPolynomialOrder source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13LaurentPolynomialOrder

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13LaurentPolynomialOrder
Original leading source comments and nonproject imports are retained below. -/
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Algebra.Polynomial.Reverse

set_option autoImplicit false




/-!
# The order at infinity of a polynomial

The substitution `X = s⁻¹` reverses a polynomial.  Its leading
coefficient becomes the constant coefficient of the reversed polynomial,
so the latter has order zero; the factor `s⁻ⁿ` accounts for the whole
order.  This is the formal local calculation used at the cusps of `X₁(13)`.
-/

open Polynomial
open scoped LaurentSeries PowerSeries

namespace MazurProof
namespace N13LaurentPolynomialOrder

noncomputable section

universe u

variable (K : Type u) [Field K]

/-- The Laurent parameter at infinity. -/
def parameter : LaurentSeries K := HahnSeries.single 1 1

/-- Evaluation of a polynomial after the substitution `X = s⁻¹`. -/
def evalAtInfinity (p : K[X]) : LaurentSeries K :=
  p.eval₂ (algebraMap K (LaurentSeries K)) (parameter K)⁻¹

@[simp] lemma parameter_ne_zero : parameter K ≠ 0 := by
  simp [parameter]

@[simp] lemma parameter_inv : (parameter K)⁻¹ = HahnSeries.single (-1 : ℤ) 1 := by
  simp [parameter, HahnSeries.inv_single]

@[simp] lemma order_parameter : (parameter K).order = 1 := by
  simp [parameter, HahnSeries.order_single]

@[simp] lemma order_parameter_inv_pow (n : ℕ) :
    ((parameter K)⁻¹ ^ n).order = -(n : ℤ) := by
  rw [parameter_inv, HahnSeries.order_pow]
  simp [HahnSeries.order_single]

lemma eval_parameter_eq_ofPowerSeries (p : K[X]) :
    p.eval₂ (algebraMap K (LaurentSeries K)) (parameter K) =
      HahnSeries.ofPowerSeries ℤ K p := by
  have h : Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K)) (parameter K) =
      algebraMap K[X] (LaurentSeries K) := by
    apply Polynomial.ringHom_ext
    · intro a
      change Polynomial.eval₂ (algebraMap K (LaurentSeries K)) (parameter K) (C a) = _
      rw [Polynomial.eval₂_C, Polynomial.algebraMap_hahnSeries_apply]
      simp [HahnSeries.algebraMap_apply']
    · change Polynomial.eval₂ (algebraMap K (LaurentSeries K)) (parameter K) X = _
      rw [Polynomial.eval₂_X, Polynomial.algebraMap_hahnSeries_apply]
      simp [parameter, HahnSeries.ofPowerSeries_X]
  change (Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K)) (parameter K)) p = _
  rw [h, Polynomial.algebraMap_hahnSeries_apply]

lemma order_ofPowerSeries_of_coeff_zero_ne (p : K[X]) (hp : p.coeff 0 ≠ 0) :
    (HahnSeries.ofPowerSeries ℤ K p).order = 0 := by
  have hcoeff : (HahnSeries.ofPowerSeries ℤ K p).coeff 0 ≠ 0 := by
    have hcoeff_eq : (HahnSeries.ofPowerSeries ℤ K p).coeff 0 = p.coeff 0 := by
      calc
        (HahnSeries.ofPowerSeries ℤ K p).coeff 0 = PowerSeries.coeff 0 (p : K⟦X⟧) :=
          HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) (p : K⟦X⟧) 0
        _ = p.coeff 0 := Polynomial.coeff_coe p 0
    rwa [hcoeff_eq]
  apply le_antisymm
  · exact HahnSeries.order_le_of_coeff_ne_zero hcoeff
  · rw [← HahnSeries.zero_le_orderTop_iff]
    apply HahnSeries.le_orderTop_iff_forall.mpr
    intro j hj
    rw [HahnSeries.ofPowerSeries_apply]
    apply HahnSeries.embDomain_notin_image_support
    rintro ⟨n, -, rfl⟩
    have hnonneg : (0 : ℤ) ≤ (Nat.castOrderEmbedding (α := ℤ) n : ℤ) := by
      simp
    exact (not_lt_of_ge (WithTop.coe_le_coe.mpr hnonneg)) hj

lemma order_eval_parameter_reverse (p : K[X]) (hp : p ≠ 0) :
    (p.reverse.eval₂ (algebraMap K (LaurentSeries K)) (parameter K)).order = 0 := by
  rw [eval_parameter_eq_ofPowerSeries]
  apply order_ofPowerSeries_of_coeff_zero_ne
  simpa using p.leadingCoeff_ne_zero.mpr hp

lemma evalAtInfinity_eq_reverse_mul (p : K[X]) :
    evalAtInfinity K p =
      p.reverse.eval₂ (algebraMap K (LaurentSeries K)) (parameter K) *
        (parameter K)⁻¹ ^ p.natDegree := by
  letI : Invertible ((parameter K)⁻¹) :=
    invertibleOfNonzero (inv_ne_zero (parameter_ne_zero K))
  symm
  unfold evalAtInfinity parameter
  simpa [Polynomial.reverse, HahnSeries.inv_single, invOf_eq_inv] using
    (Polynomial.eval₂_reflect_mul_pow (algebraMap K (LaurentSeries K))
      ((parameter K)⁻¹) p.natDegree p le_rfl)

theorem order_evalAtInfinity (p : K[X]) (hp : p ≠ 0) :
    (evalAtInfinity K p).order = -(p.natDegree : ℤ) := by
  rw [evalAtInfinity_eq_reverse_mul, HahnSeries.order_mul]
  · rw [order_eval_parameter_reverse K p hp, order_parameter_inv_pow]
    simp
  · rw [eval_parameter_eq_ofPowerSeries]
    intro hzero
    apply hp
    apply Polynomial.reverse_eq_zero.mp
    apply Polynomial.coe_injective K
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa using hzero
  · exact pow_ne_zero _ (inv_ne_zero (parameter_ne_zero K))

end
end N13LaurentPolynomialOrder
end MazurProof


