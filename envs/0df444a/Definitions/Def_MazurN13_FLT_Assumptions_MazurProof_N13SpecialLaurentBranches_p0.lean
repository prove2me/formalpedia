-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialLaurentBranches_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialLaurentBranches_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T22:57:57.044858+00:00
-- url     : https://prove2.me/theorems/edcc0664-e541-4587-b7cc-4b24b4580358
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialLaurentBranches source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialLaurentBranches

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialLaurentBranches
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialInfinityBranchJets_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialAffineNorm_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13BranchNorm_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

Actual Laurent expansions of the GOOD characteristic-two affine model.
The branch difference is h(x), not twice a square root. The resulting
two-infinity pole bound forces deg(A)<=d and deg(B)+3<=d for A+B*y.
-/

namespace MazurProof.N13SpecialLaurentBranches

noncomputable section
open Polynomial
open scoped LaurentSeries

abbrev K := N13GoodModelTwo.F2
abbrev R := N13GoodCoordinateRingTwo.CoordinateRing
abbrev P := PowerSeries K
abbrev L := LaurentSeries K
abbrev t := N13LaurentPolynomialOrder.parameter K
abbrev base := N13BranchNorm.evalPoly K
def includeSeries : P →+* L := HahnSeries.ofPowerSeries ℤ K

theorem t_ne_zero : t ≠ 0 := N13LaurentPolynomialOrder.parameter_ne_zero K

private theorem base_X : base X = t⁻¹ := by
  simp only [base, N13BranchNorm.evalPoly, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rfl

private theorem root_relation (r : P)
    (hr : r ^ 2 + N13SpecialInfinityBranchJets.h * r - N13SpecialInfinityBranchJets.rhs = 0) :
    N13GoodCoordinateRingTwo.curvePoly.eval₂ base (t⁻¹ ^ 3 * includeSeries r) = 0 := by
  have hl := congrArg includeSeries hr
  simp only [map_sub, map_add, map_mul, map_pow, map_zero] at hl
  have hh : includeSeries N13SpecialInfinityBranchJets.h = 1 + t ^ 2 + t ^ 3 := by
    simp [N13SpecialInfinityBranchJets.h, includeSeries, N13LaurentPolynomialOrder.parameter]
  have hrhs : includeSeries N13SpecialInfinityBranchJets.rhs = t + t ^ 2 := by
    simp [N13SpecialInfinityBranchJets.rhs, includeSeries, N13LaurentPolynomialOrder.parameter]
  rw [hh, hrhs] at hl
  have he : (t⁻¹ ^ 3 * includeSeries r) ^ 2 +
      (t⁻¹ ^ 3 + t⁻¹ + 1) * (t⁻¹ ^ 3 * includeSeries r) - (t⁻¹ ^ 5 + t⁻¹ ^ 4) = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 6 t_ne_zero)
    calc
      t ^ 6 * ((t⁻¹ ^ 3 * includeSeries r) ^ 2 +
          (t⁻¹ ^ 3 + t⁻¹ + 1) * (t⁻¹ ^ 3 * includeSeries r) - (t⁻¹ ^ 5 + t⁻¹ ^ 4)) =
        (includeSeries r) ^ 2 + (1 + t ^ 2 + t ^ 3) * includeSeries r - (t + t ^ 2) := by
          field_simp [t_ne_zero]
          try ring
      _ = t ^ 6 * 0 := by rw [hl, mul_zero]
  simp only [N13GoodCoordinateRingTwo.curvePoly, N13GoodCoordinateRingTwo.hPoly,
    N13GoodCoordinateRingTwo.rhsPoly, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X,
    eval₂_C, eval₂_one, map_add, map_pow, map_one, base_X]
  linear_combination he

def plus : R →+* L := AdjoinRoot.lift base
  (t⁻¹ ^ 3 * includeSeries N13SpecialInfinityBranchJets.r₀)
  (root_relation _ N13SpecialInfinityBranchJets.r₀_relation)

def minus : R →+* L := AdjoinRoot.lift base
  (t⁻¹ ^ 3 * includeSeries N13SpecialInfinityBranchJets.r₁)
  (root_relation _ N13SpecialInfinityBranchJets.r₁_relation)

@[simp] theorem plus_xClass (p : K[X]) : plus (N13GoodCoordinateRingTwo.xClass p) = base p :=
  AdjoinRoot.lift_of _

@[simp] theorem minus_xClass (p : K[X]) : minus (N13GoodCoordinateRingTwo.xClass p) = base p :=
  AdjoinRoot.lift_of _

@[simp] theorem plus_yClass : plus N13GoodCoordinateRingTwo.yClass =
    t⁻¹ ^ 3 * includeSeries N13SpecialInfinityBranchJets.r₀ := AdjoinRoot.lift_root _

@[simp] theorem minus_yClass : minus N13GoodCoordinateRingTwo.yClass =
    t⁻¹ ^ 3 * includeSeries N13SpecialInfinityBranchJets.r₁ := AdjoinRoot.lift_root _

private theorem two_eq_zero : (2 : L) = 0 := by
  simpa only [map_ofNat, map_zero] using
    congrArg (algebraMap K L) (show (2 : K) = 0 by decide)

theorem y_branch_sum : plus N13GoodCoordinateRingTwo.yClass + minus N13GoodCoordinateRingTwo.yClass =
    -base N13GoodCoordinateRingTwo.hPoly := by
  rw [plus_yClass, minus_yClass, N13SpecialInfinityBranchJets.r₁_eq, map_sub, map_neg]
  have hh : includeSeries N13SpecialInfinityBranchJets.h = 1 + t ^ 2 + t ^ 3 := by
    simp [N13SpecialInfinityBranchJets.h, includeSeries, N13LaurentPolynomialOrder.parameter]
  rw [hh]
  simp only [N13GoodCoordinateRingTwo.hPoly, map_add, map_pow, map_one, base_X]
  change t⁻¹ ^ 3 * includeSeries N13SpecialInfinityBranchJets.r₀ +
      t⁻¹ ^ 3 * (-(1 + t ^ 2 + t ^ 3) - includeSeries N13SpecialInfinityBranchJets.r₀) =
    -(t⁻¹ ^ 3 + t⁻¹ + 1)
  field_simp [t_ne_zero]
  ring

theorem y_branch_difference : plus N13GoodCoordinateRingTwo.yClass - minus N13GoodCoordinateRingTwo.yClass =
    base N13GoodCoordinateRingTwo.hPoly := by
  have hs := y_branch_sum
  calc
    plus N13GoodCoordinateRingTwo.yClass - minus N13GoodCoordinateRingTwo.yClass =
        -(plus N13GoodCoordinateRingTwo.yClass + minus N13GoodCoordinateRingTwo.yClass) +
          2 * plus N13GoodCoordinateRingTwo.yClass := by ring
    _ = _ := by rw [hs, neg_neg, two_eq_zero, zero_mul, add_zero]

theorem linear_difference (p q : K[X]) :
    plus (N13SpecialAffineNorm.linear p q) - minus (N13SpecialAffineNorm.linear p q) =
      base (q * N13GoodCoordinateRingTwo.hPoly) := by
  simp only [N13SpecialAffineNorm.linear, map_add, map_mul, plus_xClass, minus_xClass]
  calc
    base p + base q * plus N13GoodCoordinateRingTwo.yClass -
        (base p + base q * minus N13GoodCoordinateRingTwo.yClass) =
      base q * (plus N13GoodCoordinateRingTwo.yClass - minus N13GoodCoordinateRingTwo.yClass) := by ring
    _ = _ := by rw [y_branch_difference]

theorem plus_conjugate (z : R) : plus (N13SpecialAffineNorm.conjugate z) = minus z := by
  have hz : z = N13SpecialAffineNorm.linear
      (N13GoodCoordinateRingTwo.coeff0 z) (N13GoodCoordinateRingTwo.coeffY z) :=
    (N13GoodCoordinateRingTwo.recompose z).symm
  rw [hz, N13SpecialAffineNorm.conjugate_linear]
  simp only [N13SpecialAffineNorm.linear, map_add, map_mul, plus_xClass, minus_xClass,
    map_sub, map_neg]
  linear_combination -(base (N13GoodCoordinateRingTwo.coeffY z)) * y_branch_sum

theorem branch_product (z : R) : plus z * minus z = base (N13SpecialAffineNorm.norm z) := by
  rw [← plus_conjugate, ← map_mul, N13SpecialAffineNorm.mul_conjugate, plus_xClass]

theorem plus_ne_zero (z : R) (hz : z ≠ 0) : plus z ≠ 0 := by
  have hn := N13BranchNorm.evalPoly_ne_zero K (N13SpecialAffineNorm.norm_ne_zero z hz)
  rw [← branch_product] at hn
  exact left_ne_zero_of_mul hn

theorem minus_ne_zero (z : R) (hz : z ≠ 0) : minus z ≠ 0 := by
  have hn := N13BranchNorm.evalPoly_ne_zero K (N13SpecialAffineNorm.norm_ne_zero z hz)
  rw [← branch_product] at hn
  exact right_ne_zero_of_mul hn

theorem branch_orders_add (z : R) (hz : z ≠ 0) :
    (plus z).order + (minus z).order = -((N13SpecialAffineNorm.norm z).natDegree : ℤ) := by
  calc
    (plus z).order + (minus z).order = (plus z * minus z).order :=
      (HahnSeries.order_mul (plus_ne_zero z hz) (minus_ne_zero z hz)).symm
    _ = _ := by rw [branch_product, N13BranchNorm.evalPoly_order K _
      (N13SpecialAffineNorm.norm_ne_zero z hz)]

private theorem lower_order_sub (u v : L) (d : ℕ)
    (hu : -(d : ℤ) ≤ u.order) (hv : -(d : ℤ) ≤ v.order) (hsub : u - v ≠ 0) :
    -(d : ℤ) ≤ (u - v).order := by
  rw [HahnSeries.le_order_iff_forall hsub]
  intro j hj
  rw [HahnSeries.coeff_sub,
    HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hj hu),
    HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hj hv), sub_self]

/-- In characteristic two the two infinity sheets still bound the ordinate
coefficient, because their difference is the degree-three polynomial h. -/
theorem ordinate_degree_bound (p q : K[X]) (hq : q ≠ 0) (d : ℕ)
    (hpoles : -(d : ℤ) ≤ (plus (N13SpecialAffineNorm.linear p q)).order)
    (hmoles : -(d : ℤ) ≤ (minus (N13SpecialAffineNorm.linear p q)).order) :
    q.natDegree + 3 ≤ d := by
  have hqh : q * N13GoodCoordinateRingTwo.hPoly ≠ 0 :=
    mul_ne_zero hq N13GoodCoordinateRingTwo.hPoly_monic.ne_zero
  have hdiff : plus (N13SpecialAffineNorm.linear p q) - minus (N13SpecialAffineNorm.linear p q) ≠ 0 := by
    rw [linear_difference]
    exact N13BranchNorm.evalPoly_ne_zero K hqh
  have hb := lower_order_sub _ _ d hpoles hmoles hdiff
  rw [linear_difference, N13BranchNorm.evalPoly_order K _ hqh,
    Polynomial.natDegree_mul hq N13GoodCoordinateRingTwo.hPoly_monic.ne_zero,
    N13GoodCoordinateRingTwo.hPoly_natDegree, Nat.cast_add] at hb
  omega

theorem include_order_nonnegative (r : P) : 0 ≤ (includeSeries r).order := by
  by_cases hr : r = 0
  · simp [hr]
  · have hinc : includeSeries r ≠ 0 :=
      (map_ne_zero_iff includeSeries HahnSeries.ofPowerSeries_injective).mpr hr
    rw [HahnSeries.le_order_iff_forall hinc]
    intro j hj
    change ((r : LaurentSeries K).coeff j) = 0
    rw [PowerSeries.coeff_coe, if_pos hj]

private theorem ordinate_term_lower (q : K[X]) (hq : q ≠ 0) (d : ℕ)
    (hqd : q.natDegree + 3 ≤ d) :
    -(d : ℤ) ≤ (base q * plus N13GoodCoordinateRingTwo.yClass).order := by
  by_cases hy : plus N13GoodCoordinateRingTwo.yClass = 0
  · simp [hy]
  · have hr : includeSeries N13SpecialInfinityBranchJets.r₀ ≠ 0 := by
      intro hr
      apply hy
      rw [plus_yClass, hr, mul_zero]
    have hyo := HahnSeries.order_mul (pow_ne_zero 3 (inv_ne_zero t_ne_zero)) hr
    rw [← plus_yClass, N13LaurentPolynomialOrder.order_parameter_inv_pow] at hyo
    have hr0 := include_order_nonnegative N13SpecialInfinityBranchJets.r₀
    rw [HahnSeries.order_mul (N13BranchNorm.evalPoly_ne_zero K hq) hy,
      N13BranchNorm.evalPoly_order K q hq, hyo]
    omega

/-- Both infinity pole bounds give the literal small-polynomial numerator
space needed for the degree-four finite check, without any enumeration. -/
theorem polynomial_bounds_of_two_poles (p q : K[X]) (d : ℕ)
    (hpoles : -(d : ℤ) ≤ (plus (N13SpecialAffineNorm.linear p q)).order)
    (hmoles : -(d : ℤ) ≤ (minus (N13SpecialAffineNorm.linear p q)).order) :
    p.natDegree ≤ d ∧ (q = 0 ∨ q.natDegree + 3 ≤ d) := by
  have hqbound : q = 0 ∨ q.natDegree + 3 ≤ d := by
    by_cases hq : q = 0
    · exact Or.inl hq
    · exact Or.inr (ordinate_degree_bound p q hq d hpoles hmoles)
  refine ⟨?_, hqbound⟩
  by_cases hp : p = 0
  · simp [hp]
  · by_cases hq : q = 0
    · have hb : -(d : ℤ) ≤ (base p).order := by
        simpa [N13SpecialAffineNorm.linear, hq] using hpoles
      rw [N13BranchNorm.evalPoly_order K p hp] at hb
      omega
    · have hqd : q.natDegree + 3 ≤ d := hqbound.resolve_left hq
      have hterm := ordinate_term_lower q hq d hqd
      have he : plus (N13SpecialAffineNorm.linear p q) -
          base q * plus N13GoodCoordinateRingTwo.yClass = base p := by
        simp only [N13SpecialAffineNorm.linear, map_add, map_mul, plus_xClass]
        ring
      have hne : plus (N13SpecialAffineNorm.linear p q) -
          base q * plus N13GoodCoordinateRingTwo.yClass ≠ 0 := by
        rw [he]
        exact N13BranchNorm.evalPoly_ne_zero K hp
      have hb := lower_order_sub _ _ d hpoles hterm hne
      rw [he, N13BranchNorm.evalPoly_order K p hp] at hb
      omega

theorem degree_four_polynomial_bounds (p q : K[X])
    (hpoles : (-4 : ℤ) ≤ (plus (N13SpecialAffineNorm.linear p q)).order)
    (hmoles : (-4 : ℤ) ≤ (minus (N13SpecialAffineNorm.linear p q)).order) :
    p.natDegree ≤ 4 ∧ q.natDegree ≤ 1 := by
  obtain ⟨hp, hq⟩ := polynomial_bounds_of_two_poles p q 4 hpoles hmoles
  refine ⟨hp, ?_⟩
  rcases hq with hq | hq
  · simp [hq]
  · omega

end
end MazurProof.N13SpecialLaurentBranches


