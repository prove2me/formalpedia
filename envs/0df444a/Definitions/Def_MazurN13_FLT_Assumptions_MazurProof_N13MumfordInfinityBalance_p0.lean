-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordInfinityBalance_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13MumfordInfinityBalance_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:10:35.596162+00:00
-- url     : https://prove2.me/theorems/ba017250-d74d-4f1e-82e8-634971d4bf9d
-- title:
--   FLT.Assumptions.MazurProof.N13MumfordInfinityBalance source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13MumfordInfinityBalance

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13MumfordInfinityBalance
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordStructuralReduction_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13BranchLeading_p0

set_option autoImplicit false




/-!
# Structural infinity balancing for the true `X₁(13)` sextic

The polynomial used here is exactly

`X⁶ + 4X⁵ + 6X⁴ + 2X³ + X² + 2X + 1`.

Its positive-infinity cubic part is

`s = X³ + 2X² + X - 1`,

with the exact low-degree identity `f - s² = 4X(X+1)`.  This file builds
the two adapted Cantor lifts needed to balance the integer at infinity.
There is no divisor enumeration or Riemann--Roch input.
-/

open Polynomial
open scoped LaurentSeries nonZeroDivisors

namespace MazurProof.N13MumfordInfinityBalance

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K]

open MazurProof
open MazurProof.SexticMumford

abbrev M : SexticMumford.Model K := N13Mumford.model K

/-- Polynomial part of the positive branch `Y` at infinity. -/
def sqrtInfinity : K[X] :=
  X ^ 3 + 2 * X ^ 2 + X - 1

theorem sqrtInfinity_isMonicOfDegree :
    IsMonicOfDegree (sqrtInfinity : K[X]) 3 := by
  constructor
  · unfold sqrtInfinity
    compute_degree!
  · unfold sqrtInfinity
    monicity!

@[simp] theorem sqrtInfinity_natDegree :
    (sqrtInfinity : K[X]).natDegree = 3 :=
  sqrtInfinity_isMonicOfDegree.natDegree_eq

omit [CharZero K] in
theorem f_sub_sqrtInfinity_sq :
    N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2 =
      4 * X * (X + 1) := by
  simp only [N13Mumford.f, sqrtInfinity]
  ring

omit [CharZero K] in
theorem f_sub_sqrtInfinity_sq_natDegree_le :
    (N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2).natDegree ≤ 2 := by
  rw [f_sub_sqrtInfinity_sq]
  compute_degree!

variable (D : N13Mumford.SemiMumford K)

/-! ## The two adapted lifts -/

def plusRemainder : K[X] :=
  (sqrtInfinity - D.v) % D.u

/-- Congruent to `v` and monic cubic; adapted to the positive branch. -/
def plusLift : K[X] :=
  sqrtInfinity - plusRemainder D

def minusRemainder : K[X] :=
  (-sqrtInfinity - D.v) % D.u

/-- Congruent to `v`, with `-minusLift` monic cubic. -/
def minusLift : K[X] :=
  -sqrtInfinity - minusRemainder D

omit [CharZero K] in
private theorem sub_mod_dvd
    (p u : K[X]) :
    u ∣ p - p % u := by
  refine ⟨p / u, ?_⟩
  have hdiv := EuclideanDomain.mod_add_div p u
  calc
    p - p % u =
        (p % u + u * (p / u)) - p % u := by rw [hdiv]
    _ = u * (p / u) := by ring

theorem plusLift_congr :
    D.u ∣ plusLift D - D.v := by
  unfold plusLift plusRemainder
  convert sub_mod_dvd (sqrtInfinity - D.v) D.u using 1
  all_goals ring

theorem minusLift_congr :
    D.u ∣ minusLift D - D.v := by
  unfold minusLift minusRemainder
  convert sub_mod_dvd (-sqrtInfinity - D.v) D.u using 1
  all_goals ring

private theorem curve_dvd_of_congr
    (V : K[X]) (hV : D.u ∣ V - D.v) :
    D.u ∣ N13Mumford.f K - V ^ 2 := by
  obtain ⟨a, ha⟩ := D.curve_dvd
  change N13Mumford.f K - D.v ^ 2 = D.u * a at ha
  obtain ⟨b, hb⟩ := hV
  refine ⟨a - b * (V + D.v), ?_⟩
  calc
    N13Mumford.f K - V ^ 2 =
        (N13Mumford.f K - D.v ^ 2) -
          (V - D.v) * (V + D.v) := by ring
    _ = D.u * a - (D.u * b) * (V + D.v) := by
          rw [ha, hb]
    _ = D.u * (a - b * (V + D.v)) := by ring

theorem plusLift_curve_dvd :
    D.u ∣ N13Mumford.f K - (plusLift D) ^ 2 :=
  curve_dvd_of_congr D (plusLift D) (plusLift_congr D)

theorem minusLift_curve_dvd :
    D.u ∣ N13Mumford.f K - (minusLift D) ^ 2 :=
  curve_dvd_of_congr D (minusLift D) (minusLift_congr D)

def plusFactor : K[X] :=
  Classical.choose (plusLift_curve_dvd D)

theorem plusFactor_spec :
    N13Mumford.f K - (plusLift D) ^ 2 =
      D.u * plusFactor D :=
  Classical.choose_spec (plusLift_curve_dvd D)

def minusFactor : K[X] :=
  Classical.choose (minusLift_curve_dvd D)

theorem minusFactor_spec :
    N13Mumford.f K - (minusLift D) ^ 2 =
      D.u * minusFactor D :=
  Classical.choose_spec (minusLift_curve_dvd D)

theorem plusFactor_ne_zero :
    plusFactor D ≠ 0 :=
  cantorFactor_ne_zero (N13Mumford.model K)
    D.u (plusLift D) (plusFactor D) (plusFactor_spec D)

theorem minusFactor_ne_zero :
    minusFactor D ≠ 0 :=
  cantorFactor_ne_zero (N13Mumford.model K)
    D.u (minusLift D) (minusFactor D) (minusFactor_spec D)

/-! ## Degree bounds -/

private theorem mod_natDegree_lt
    (p : K[X]) (hpos : 0 < D.u.natDegree) :
    (p % D.u).natDegree < D.u.natDegree := by
  by_cases hr : p % D.u = 0
  · rw [hr]
    simp
    exact hpos
  · exact natDegree_lt_natDegree hr
      (degree_mod_lt p D.u_monic.ne_zero)

private theorem mod_eq_zero_of_natDegree_eq_zero
    (p : K[X]) (hzero : D.u.natDegree = 0) :
    p % D.u = 0 := by
  have hu : D.u = 1 :=
    eq_one_of_monic_natDegree_zero D.u_monic hzero
  rw [hu]
  simp

theorem plusRemainder_natDegree_lt
    (hpos : 0 < D.u.natDegree) :
    (plusRemainder D).natDegree < D.u.natDegree :=
  mod_natDegree_lt D (sqrtInfinity - D.v) hpos

theorem minusRemainder_natDegree_lt
    (hpos : 0 < D.u.natDegree) :
    (minusRemainder D).natDegree < D.u.natDegree :=
  mod_natDegree_lt D (-sqrtInfinity - D.v) hpos

theorem plusRemainder_eq_zero
    (hzero : D.u.natDegree = 0) :
    plusRemainder D = 0 :=
  mod_eq_zero_of_natDegree_eq_zero D _ hzero

theorem minusRemainder_eq_zero
    (hzero : D.u.natDegree = 0) :
    minusRemainder D = 0 :=
  mod_eq_zero_of_natDegree_eq_zero D _ hzero

theorem plusRemainder_natDegree_le_one
    (hdeg : D.u.natDegree ≤ 2) :
    (plusRemainder D).natDegree ≤ 1 := by
  by_cases hzero : D.u.natDegree = 0
  · rw [plusRemainder_eq_zero D hzero]
    simp
  · have hpos : 0 < D.u.natDegree := Nat.pos_of_ne_zero hzero
    have hlt := plusRemainder_natDegree_lt D hpos
    omega

theorem minusRemainder_natDegree_le_one
    (hdeg : D.u.natDegree ≤ 2) :
    (minusRemainder D).natDegree ≤ 1 := by
  by_cases hzero : D.u.natDegree = 0
  · rw [minusRemainder_eq_zero D hzero]
    simp
  · have hpos : 0 < D.u.natDegree := Nat.pos_of_ne_zero hzero
    have hlt := minusRemainder_natDegree_lt D hpos
    omega

theorem plusLift_isMonicOfDegree
    (hdeg : D.u.natDegree ≤ 2) :
    IsMonicOfDegree (plusLift D) 3 := by
  unfold plusLift
  exact sqrtInfinity_isMonicOfDegree.sub
    (by have := plusRemainder_natDegree_le_one D hdeg; omega)

theorem neg_minusLift_isMonicOfDegree
    (hdeg : D.u.natDegree ≤ 2) :
    IsMonicOfDegree (-minusLift D) 3 := by
  have hmonic :
      IsMonicOfDegree
        (sqrtInfinity + minusRemainder D : K[X]) 3 :=
    sqrtInfinity_isMonicOfDegree.add_right
      (by have := minusRemainder_natDegree_le_one D hdeg; omega)
  convert hmonic using 1
  unfold minusLift
  ring

private theorem two_mul_sqrt_mul_natDegree_le
    (r : K[X]) {d : ℕ} (hr : r.natDegree < d) :
    (2 * (sqrtInfinity : K[X]) * r).natDegree ≤ d + 2 := by
  calc
    (2 * (sqrtInfinity : K[X]) * r).natDegree ≤
        (2 * (sqrtInfinity : K[X])).natDegree + r.natDegree :=
      natDegree_mul_le
    _ ≤ ((2 : K[X]).natDegree +
          (sqrtInfinity : K[X]).natDegree) + r.natDegree := by
      gcongr
      exact natDegree_mul_le
    _ = 3 + r.natDegree := by simp
    _ ≤ d + 2 := by omega

omit [CharZero K] in
private theorem remainder_sq_natDegree_le
    (r : K[X]) {d : ℕ} (hd : d ≤ 2) (hr : r.natDegree < d) :
    (r ^ 2).natDegree ≤ d + 2 := by
  rw [natDegree_pow]
  omega

private theorem adaptedNumerator_natDegree_le
    (r : K[X]) {d : ℕ} (hd : d ≤ 2)
    (hr : r.natDegree < d) :
    ((N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2) +
        2 * sqrtInfinity * r - r ^ 2).natDegree ≤ d + 2 := by
  have hbase :
      (N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2).natDegree ≤
        d + 2 :=
    (f_sub_sqrtInfinity_sq_natDegree_le (K := K)).trans (by omega)
  have hmiddle :
      (2 * (sqrtInfinity : K[X]) * r).natDegree ≤ d + 2 :=
    two_mul_sqrt_mul_natDegree_le r hr
  have hsquare : (r ^ 2).natDegree ≤ d + 2 :=
    remainder_sq_natDegree_le r hd hr
  exact
    (natDegree_sub_le _ _).trans <|
      (Nat.max_le.mpr
        ⟨(natDegree_add_le _ _).trans
            (Nat.max_le.mpr ⟨hbase, hmiddle⟩),
          hsquare⟩)

private theorem adaptedNumeratorNeg_natDegree_le
    (r : K[X]) {d : ℕ} (hd : d ≤ 2)
    (hr : r.natDegree < d) :
    ((N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2) -
        2 * sqrtInfinity * r - r ^ 2).natDegree ≤ d + 2 := by
  have hbase :
      (N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2).natDegree ≤
        d + 2 :=
    (f_sub_sqrtInfinity_sq_natDegree_le (K := K)).trans (by omega)
  have hmiddle :
      (2 * (sqrtInfinity : K[X]) * r).natDegree ≤ d + 2 :=
    two_mul_sqrt_mul_natDegree_le r hr
  have hsquare : (r ^ 2).natDegree ≤ d + 2 :=
    remainder_sq_natDegree_le r hd hr
  exact
    (natDegree_sub_le _ _).trans <|
      (Nat.max_le.mpr
        ⟨(natDegree_sub_le _ _).trans
            (Nat.max_le.mpr ⟨hbase, hmiddle⟩),
          hsquare⟩)

theorem plusNumerator_natDegree_le
    (hdeg : D.u.natDegree ≤ 2) :
    (N13Mumford.f K - (plusLift D) ^ 2).natDegree ≤
      D.u.natDegree + 2 := by
  by_cases hzero : D.u.natDegree = 0
  · rw [plusLift, plusRemainder_eq_zero D hzero]
    simp only [sub_zero]
    exact (f_sub_sqrtInfinity_sq_natDegree_le (K := K)).trans
      (by omega)
  · have hpos : 0 < D.u.natDegree := Nat.pos_of_ne_zero hzero
    rw [show N13Mumford.f K - (plusLift D) ^ 2 =
      (N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2) +
        2 * sqrtInfinity * plusRemainder D -
          (plusRemainder D) ^ 2 by
      unfold plusLift
      ring]
    exact adaptedNumerator_natDegree_le
      (plusRemainder D) hdeg (plusRemainder_natDegree_lt D hpos)

theorem minusNumerator_natDegree_le
    (hdeg : D.u.natDegree ≤ 2) :
    (N13Mumford.f K - (minusLift D) ^ 2).natDegree ≤
      D.u.natDegree + 2 := by
  by_cases hzero : D.u.natDegree = 0
  · rw [minusLift, minusRemainder_eq_zero D hzero]
    simp only [sub_zero, neg_sq]
    exact (f_sub_sqrtInfinity_sq_natDegree_le (K := K)).trans
      (by omega)
  · have hpos : 0 < D.u.natDegree := Nat.pos_of_ne_zero hzero
    rw [show N13Mumford.f K - (minusLift D) ^ 2 =
      (N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2) -
        2 * sqrtInfinity * minusRemainder D -
          (minusRemainder D) ^ 2 by
      unfold minusLift
      ring]
    exact adaptedNumeratorNeg_natDegree_le
      (minusRemainder D) hdeg (minusRemainder_natDegree_lt D hpos)

theorem plusFactor_natDegree_le_two
    (hdeg : D.u.natDegree ≤ 2) :
    (plusFactor D).natDegree ≤ 2 := by
  have hsum :
      D.u.natDegree + (plusFactor D).natDegree =
        (N13Mumford.f K - (plusLift D) ^ 2).natDegree := by
    rw [← natDegree_mul D.u_monic.ne_zero
      (plusFactor_ne_zero D), ← plusFactor_spec D]
  have hnum := plusNumerator_natDegree_le D hdeg
  omega

theorem minusFactor_natDegree_le_two
    (hdeg : D.u.natDegree ≤ 2) :
    (minusFactor D).natDegree ≤ 2 := by
  have hsum :
      D.u.natDegree + (minusFactor D).natDegree =
        (N13Mumford.f K - (minusLift D) ^ 2).natDegree := by
    rw [← natDegree_mul D.u_monic.ne_zero
      (minusFactor_ne_zero D), ← minusFactor_spec D]
  have hnum := minusNumerator_natDegree_le D hdeg
  omega

/-! ## Leading terms at the two infinities -/

omit [CharZero K] in
private theorem evalPoly_coeff_neg_three_eq_zero
    (p : K[X]) (hdeg : p.natDegree ≤ 2) :
    (N13BranchNorm.evalPoly K p).coeff (-3 : ℤ) = 0 := by
  by_cases hp : p = 0
  · simp [hp]
  · by_contra hcoeff
    have horder :
        (N13BranchNorm.evalPoly K p).order ≤ (-3 : ℤ) :=
      HahnSeries.order_le_of_coeff_ne_zero hcoeff
    rw [N13BranchNorm.evalPoly_order K p hp] at horder
    omega

omit [CharZero K] in
private theorem evalSqrtInfinity_coeff_neg_three :
    (N13BranchNorm.evalPoly K (sqrtInfinity : K[X])).coeff
        (-3 : ℤ) = 1 := by
  simp [N13BranchNorm.evalPoly, sqrtInfinity,
    N13Infinity.parameter]
  change ((2 : LaurentSeries K) *
    HahnSeries.single (-2 : ℤ) 1).coeff (-3 : ℤ) = 0
  rw [show (2 : LaurentSeries K) =
    HahnSeries.single (0 : ℤ) 2 by rfl]
  rw [HahnSeries.coeff_single_mul]
  norm_num [HahnSeries.coeff_single]

private theorem wSeries_coeff_zero :
    (N13Infinity.wSeries K).coeff (0 : ℤ) = 1 := by
  change (HahnSeries.ofPowerSeries ℤ K
    (N13Infinity.sqrtReverseF K)).coeff (0 : ℕ) = 1
  rw [HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff,
    N13Infinity.sqrtReverseF_constantCoeff]

private theorem ySeries_coeff_neg_three :
    (N13Infinity.ySeries K).coeff (-3 : ℤ) = 1 := by
  simp only [N13Infinity.ySeries, N13Infinity.parameter,
    HahnSeries.inv_single, inv_one,
    HahnSeries.single_pow, one_pow]
  rw [HahnSeries.coeff_single_mul]
  norm_num
  exact wSeries_coeff_zero (K := K)

theorem evalPlusLift_coeff_neg_three
    (hdeg : D.u.natDegree ≤ 2) :
    (N13BranchNorm.evalPoly K (plusLift D)).coeff (-3 : ℤ) = 1 := by
  rw [plusLift, map_sub, HahnSeries.coeff_sub,
    evalSqrtInfinity_coeff_neg_three]
  rw [evalPoly_coeff_neg_three_eq_zero
    (plusRemainder D) (by
      exact (plusRemainder_natDegree_le_one D hdeg).trans (by omega))]
  norm_num

theorem evalNegMinusLift_coeff_neg_three
    (hdeg : D.u.natDegree ≤ 2) :
    (N13BranchNorm.evalPoly K (-minusLift D)).coeff (-3 : ℤ) = 1 := by
  rw [show -minusLift D =
      sqrtInfinity + minusRemainder D by
        unfold minusLift
        ring,
    map_add, HahnSeries.coeff_add,
    evalSqrtInfinity_coeff_neg_three]
  rw [evalPoly_coeff_neg_three_eq_zero
    (minusRemainder D) (by
      exact (minusRemainder_natDegree_le_one D hdeg).trans (by omega))]
  norm_num

private theorem linearFunction_neg_eq_ySubClass
    (V : K[X]) :
    N13BranchNorm.linearFunction K (-V) 1 =
      ySubClass (N13Mumford.model K) V := by
  simp [N13BranchNorm.linearFunction, ySubClass]
  ring

private theorem branch_order_lower_bounds_of_natDegree_three
    (V : K[X]) (hV : V.natDegree = 3) :
    (-3 : ℤ) ≤
        (N13Infinity.coordinateToLaurent K
          (ySubClass (N13Mumford.model K) V)).order ∧
      (-3 : ℤ) ≤
        (N13InfinityMinus.coordinateToLaurentMinus K
          (ySubClass (N13Mumford.model K) V)).order := by
  have hlinear := linearFunction_neg_eq_ySubClass (K := K) V
  have hmin := N13BranchLeading.branch_min_order K (-V) 1
    (by
      rw [hlinear]
      exact ySubClass_ne_zero (N13Mumford.model K) V)
  rw [hlinear] at hmin
  have hpole :
      N13BranchLeading.poleDegree K (-V) 1 = 3 := by
    simp [N13BranchLeading.poleDegree, hV]
  rw [hpole] at hmin
  constructor <;> omega

theorem plusYSub_minus_coeff_neg_three
    (hdeg : D.u.natDegree ≤ 2) :
    (N13InfinityMinus.coordinateToLaurentMinus K
      (ySubClass (N13Mumford.model K) (plusLift D))).coeff
        (-3 : ℤ) = -2 := by
  rw [ySubClass, map_sub,
    N13InfinityMinus.coordinateToLaurentMinus_yClass,
    N13InfinityMinus.coordinateToLaurentMinus_xClass]
  change
    (N13InfinityMinus.ySeriesMinus K -
      N13BranchNorm.evalPoly K (plusLift D)).coeff (-3 : ℤ) = -2
  rw [N13InfinityMinus.ySeriesMinus_eq_neg,
    HahnSeries.coeff_sub, HahnSeries.coeff_neg,
    ySeries_coeff_neg_three,
    evalPlusLift_coeff_neg_three D hdeg]
  norm_num

theorem minusYSub_plus_coeff_neg_three
    (hdeg : D.u.natDegree ≤ 2) :
    (N13Infinity.coordinateToLaurent K
      (ySubClass (N13Mumford.model K) (minusLift D))).coeff
        (-3 : ℤ) = 2 := by
  rw [ySubClass, map_sub,
    N13BranchNorm.coordinateToLaurent_yClass,
    N13Infinity.coordinateToLaurent_xClass]
  change
    (N13Infinity.ySeries K -
      N13BranchNorm.evalPoly K (minusLift D)).coeff (-3 : ℤ) = 2
  have hneg :
      N13BranchNorm.evalPoly K (minusLift D) =
        -N13BranchNorm.evalPoly K (-minusLift D) := by
    simp
  rw [hneg, HahnSeries.coeff_sub, HahnSeries.coeff_neg,
    ySeries_coeff_neg_three,
    evalNegMinusLift_coeff_neg_three D hdeg]
  norm_num

theorem plusYSub_minus_order
    (hdeg : D.u.natDegree ≤ 2) :
    (N13InfinityMinus.coordinateToLaurentMinus K
      (ySubClass (N13Mumford.model K) (plusLift D))).order = -3 := by
  have hlower :=
    (branch_order_lower_bounds_of_natDegree_three
      (K := K) (plusLift D)
      (plusLift_isMonicOfDegree D hdeg).natDegree_eq).2
  have hupper :
      (N13InfinityMinus.coordinateToLaurentMinus K
        (ySubClass (N13Mumford.model K) (plusLift D))).order ≤
          (-3 : ℤ) :=
    HahnSeries.order_le_of_coeff_ne_zero (by
      rw [plusYSub_minus_coeff_neg_three D hdeg]
      norm_num)
  exact le_antisymm hupper hlower

theorem minusYSub_plus_order
    (hdeg : D.u.natDegree ≤ 2) :
    (N13Infinity.coordinateToLaurent K
      (ySubClass (N13Mumford.model K) (minusLift D))).order = -3 := by
  have hlower :=
    (branch_order_lower_bounds_of_natDegree_three
      (K := K) (minusLift D)
      (by
        rw [← natDegree_neg]
        exact (neg_minusLift_isMonicOfDegree D hdeg).natDegree_eq)).1
  have hupper :
      (N13Infinity.coordinateToLaurent K
        (ySubClass (N13Mumford.model K) (minusLift D))).order ≤
          (-3 : ℤ) :=
    HahnSeries.order_le_of_coeff_ne_zero (by
      rw [minusYSub_plus_coeff_neg_three D hdeg]
      norm_num)
  exact le_antisymm hupper hlower

/-! ## Exact orders of the principal Cantor corrections -/

theorem plusNormNumerator_eq :
    N13BranchNorm.normNumerator K (-(plusLift D)) 1 =
      -(D.u * plusFactor D) := by
  simp only [N13BranchNorm.normNumerator, neg_sq, one_pow, one_mul]
  rw [← plusFactor_spec D]
  ring

theorem plusNormNumerator_ne_zero :
    N13BranchNorm.normNumerator K (-(plusLift D)) 1 ≠ 0 := by
  rw [plusNormNumerator_eq D]
  exact neg_ne_zero.mpr
    (mul_ne_zero D.u_monic.ne_zero (plusFactor_ne_zero D))

theorem plusNormNumerator_natDegree :
    (N13BranchNorm.normNumerator K (-(plusLift D)) 1).natDegree =
      D.u.natDegree + (plusFactor D).natDegree := by
  rw [plusNormNumerator_eq D, natDegree_neg,
    natDegree_mul D.u_monic.ne_zero (plusFactor_ne_zero D)]

theorem plusYSub_branch_orders_add :
    (N13Infinity.coordinateToLaurent K
        (ySubClass (N13Mumford.model K) (plusLift D))).order +
      (N13InfinityMinus.coordinateToLaurentMinus K
        (ySubClass (N13Mumford.model K) (plusLift D))).order =
      -((D.u.natDegree + (plusFactor D).natDegree : ℕ) : ℤ) := by
  have hsum := N13BranchNorm.branch_orders_add K
    (-(plusLift D)) 1 (plusNormNumerator_ne_zero D)
  rw [linearFunction_neg_eq_ySubClass] at hsum
  rw [plusNormNumerator_natDegree D] at hsum
  exact hsum

theorem plusYSub_plus_order
    (hdeg : D.u.natDegree ≤ 2) :
    (N13Infinity.coordinateToLaurent K
      (ySubClass (N13Mumford.model K) (plusLift D))).order =
        3 - (D.u.natDegree : ℤ) -
          ((plusFactor D).natDegree : ℤ) := by
  have hsum := plusYSub_branch_orders_add D
  have hminus := plusYSub_minus_order D hdeg
  omega

theorem ordPlus_ySubFunctionUnit
    (V : K[X]) :
    Multiplicative.toAdd
      ((N13Infinity.positiveInfinityOrder K).ordPlus
        (ySubFunctionUnit (N13Mumford.model K) V)) =
      (N13Infinity.coordinateToLaurent K
        (ySubClass (N13Mumford.model K) V)).order := by
  change
    (N13Infinity.functionFieldToLaurent K
      (algebraMap
        (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)
        (ySubClass (N13Mumford.model K) V))).order = _
  rw [N13Infinity.functionFieldToLaurent_algebraMap]

theorem ordPlus_xClassFunctionUnit
    (p : K[X]) (hp : p ≠ 0) :
    Multiplicative.toAdd
      ((N13Infinity.positiveInfinityOrder K).ordPlus
        (xClassFunctionUnit (N13Mumford.model K) p hp)) =
      -(p.natDegree : ℤ) := by
  change
    (N13Infinity.functionFieldToLaurent K
      (algebraMap
        (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)
        (xClass (N13Mumford.model K) p))).order =
      -(p.natDegree : ℤ)
  rw [N13Infinity.functionFieldToLaurent_algebraMap,
    N13Infinity.coordinateToLaurent_xClass]
  exact N13BranchNorm.evalPoly_order K p hp

theorem plusCorrection_order
    (hdeg : D.u.natDegree ≤ 2) :
    Multiplicative.toAdd
      ((N13Infinity.positiveInfinityOrder K).ordPlus
        (cantorCorrectionUnit (N13Mumford.model K)
          (plusLift D) (plusFactor D) (plusFactor_ne_zero D))) =
      3 - (D.u.natDegree : ℤ) := by
  rw [cantorCorrectionUnit, map_mul, map_inv,
    toAdd_mul, toAdd_inv,
    ordPlus_ySubFunctionUnit,
    ordPlus_xClassFunctionUnit,
    plusYSub_plus_order D hdeg,
    natDegree_normalize_eq]
  ring

theorem minusCorrection_order
    (hdeg : D.u.natDegree ≤ 2) :
    Multiplicative.toAdd
      ((N13Infinity.positiveInfinityOrder K).ordPlus
        (cantorCorrectionUnit (N13Mumford.model K)
          (minusLift D) (minusFactor D) (minusFactor_ne_zero D))) =
      (minusFactor D).natDegree - 3 := by
  rw [cantorCorrectionUnit, map_mul, map_inv,
    toAdd_mul, toAdd_inv,
    ordPlus_ySubFunctionUnit,
    ordPlus_xClassFunctionUnit,
    minusYSub_plus_order D hdeg,
    natDegree_normalize_eq]
  ring

/-! ## The two class-preserving balancing steps -/

def plusStep :
    N13Mumford.SemiMumford K :=
  cantorNextSemi (N13Mumford.model K)
    (N13Infinity.positiveInfinityOrder K) D
    (plusLift D) (plusFactor D)
    (plusFactor_spec D) (plusFactor_ne_zero D)

def minusStep :
    N13Mumford.SemiMumford K :=
  cantorNextSemi (N13Mumford.model K)
    (N13Infinity.positiveInfinityOrder K) D
    (minusLift D) (minusFactor D)
    (minusFactor_spec D) (minusFactor_ne_zero D)

@[simp] theorem plusStep_nInf
    (hdeg : D.u.natDegree ≤ 2) :
    (plusStep D).nInf =
      D.nInf + (D.u.natDegree : ℤ) - 3 := by
  change D.nInf - Multiplicative.toAdd
    ((N13Infinity.positiveInfinityOrder K).ordPlus
      (cantorCorrectionUnit (N13Mumford.model K)
        (plusLift D) (plusFactor D) (plusFactor_ne_zero D))) = _
  rw [plusCorrection_order D hdeg]
  ring

@[simp] theorem minusStep_nInf
    (hdeg : D.u.natDegree ≤ 2) :
    (minusStep D).nInf =
      D.nInf + 3 - (minusFactor D).natDegree := by
  change D.nInf - Multiplicative.toAdd
    ((N13Infinity.positiveInfinityOrder K).ordPlus
      (cantorCorrectionUnit (N13Mumford.model K)
        (minusLift D) (minusFactor D) (minusFactor_ne_zero D))) = _
  rw [minusCorrection_order D hdeg]
  ring

@[simp] theorem plusStep_natDegree :
    (plusStep D).u.natDegree = (plusFactor D).natDegree := by
  exact cantorNextSemi_natDegree (N13Mumford.model K)
    (N13Infinity.positiveInfinityOrder K) D (plusLift D) (plusFactor D)
    (plusFactor_spec D) (plusFactor_ne_zero D)

@[simp] theorem minusStep_natDegree :
    (minusStep D).u.natDegree = (minusFactor D).natDegree := by
  exact cantorNextSemi_natDegree (N13Mumford.model K)
    (N13Infinity.positiveInfinityOrder K) D (minusLift D) (minusFactor D)
    (minusFactor_spec D) (minusFactor_ne_zero D)

private theorem adaptedBezout
    (V w : K[X])
    (hcurve : N13Mumford.f K - V ^ 2 = D.u * w)
    (hcongr : D.u ∣ V - D.v) :
    ∃ a b c : K[X],
      a * D.u + b * (2 * V) + c * w = 1 := by
  obtain ⟨t, ht⟩ := hcongr
  have hV : V = D.v + D.u * t := by
    linear_combination ht
  rw [hV]
  exact cantorBezout_add_mul (N13Mumford.model K) D t w
    (by simpa only [N13Mumford.model_f, hV] using hcurve)

theorem plusStep_class :
    semiMumfordClass (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K) (plusStep D) =
      semiMumfordClass (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K) D := by
  unfold plusStep
  apply cantorNextSemi_class
    (N13Mumford.model K) (N13Infinity.positiveInfinityOrder K)
    D (plusLift D) (plusFactor D)
    (plusFactor_spec D) (plusFactor_ne_zero D)
    (plusLift_congr D)
  exact adaptedBezout D (plusLift D) (plusFactor D)
    (plusFactor_spec D) (plusLift_congr D)

theorem minusStep_class :
    semiMumfordClass (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K) (minusStep D) =
      semiMumfordClass (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K) D := by
  unfold minusStep
  apply cantorNextSemi_class
    (N13Mumford.model K) (N13Infinity.positiveInfinityOrder K)
    D (minusLift D) (minusFactor D)
    (minusFactor_spec D) (minusFactor_ne_zero D)
    (minusLift_congr D)
  exact adaptedBezout D (minusLift D) (minusFactor D)
    (minusFactor_spec D) (minusLift_congr D)

abbrev LowDegree :
    Type u :=
  LowDegreeSemi (N13Mumford.model K)

def plusStepLow (E : LowDegree (K := K)) :
    LowDegree (K := K) where
  toSemi := plusStep E.toSemi
  degree_le_two := by
    rw [plusStep_natDegree]
    exact plusFactor_natDegree_le_two E.toSemi E.degree_le_two

def minusStepLow (E : LowDegree (K := K)) :
    LowDegree (K := K) where
  toSemi := minusStep E.toSemi
  degree_le_two := by
    rw [minusStep_natDegree]
    exact minusFactor_natDegree_le_two E.toSemi E.degree_le_two

theorem minusStep_nInf_gt
    (E : LowDegree (K := K)) :
    E.toSemi.nInf < (minusStep E.toSemi).nInf := by
  have he :=
    minusFactor_natDegree_le_two E.toSemi E.degree_le_two
  rw [minusStep_nInf E.toSemi E.degree_le_two]
  omega

theorem minusStep_upper_wall
    (E : LowDegree (K := K)) (_hn : E.toSemi.nInf < 0) :
    ((minusStep E.toSemi).u.natDegree : ℤ) +
        (minusStep E.toSemi).nInf ≤ 2 := by
  have he :=
    minusFactor_natDegree_le_two E.toSemi E.degree_le_two
  rw [minusStep_natDegree,
    minusStep_nInf E.toSemi E.degree_le_two]
  omega

theorem plusStep_lower_wall
    (E : LowDegree (K := K))
    (hhigh : 2 <
      (E.toSemi.u.natDegree : ℤ) + E.toSemi.nInf) :
    0 ≤ (plusStep E.toSemi).nInf := by
  rw [plusStep_nInf E.toSemi E.degree_le_two]
  omega

theorem plusStep_upper_excess_lt
    (E : LowDegree (K := K)) :
    ((plusStep E.toSemi).u.natDegree : ℤ) +
          (plusStep E.toSemi).nInf - 2 <
      (E.toSemi.u.natDegree : ℤ) + E.toSemi.nInf - 2 := by
  have he :=
    plusFactor_natDegree_le_two E.toSemi E.degree_le_two
  rw [plusStep_natDegree,
    plusStep_nInf E.toSemi E.degree_le_two]
  omega

/-! ## A well-founded measure for the two balance walls -/

def lowerDefect (E : LowDegree (K := K)) : ℕ :=
  Int.toNat (-E.toSemi.nInf)

def upperDefect (E : LowDegree (K := K)) : ℕ :=
  Int.toNat
    ((E.toSemi.u.natDegree : ℤ) + E.toSemi.nInf - 2)

def imbalance (E : LowDegree (K := K)) : ℕ :=
  lowerDefect E + upperDefect E

def IsBalanced (E : LowDegree (K := K)) : Prop :=
  0 ≤ E.toSemi.nInf ∧
    (E.toSemi.u.natDegree : ℤ) + E.toSemi.nInf ≤ 2

theorem imbalance_eq_zero_iff
    (E : LowDegree (K := K)) :
    imbalance E = 0 ↔ IsBalanced E := by
  simp only [imbalance, Nat.add_eq_zero_iff, lowerDefect, upperDefect,
    Int.toNat_eq_zero, IsBalanced]
  omega

theorem imbalance_minusStepLow_lt
    (E : LowDegree (K := K)) (hn : E.toSemi.nInf < 0) :
    imbalance (minusStepLow E) < imbalance E := by
  have hgt := minusStep_nInf_gt E
  have hnewUpper := minusStep_upper_wall E hn
  have holdUpper :
      upperDefect E = 0 := by
    rw [upperDefect, Int.toNat_eq_zero]
    have hd := E.degree_le_two
    omega
  have hnextUpper :
      upperDefect (minusStepLow E) = 0 := by
    rw [upperDefect, Int.toNat_eq_zero]
    exact sub_nonpos.mpr hnewUpper
  rw [imbalance, imbalance, holdUpper, hnextUpper,
    Nat.add_zero, Nat.add_zero]
  apply (Int.toNat_lt_toNat (by omega)).2
  change -(minusStep E.toSemi).nInf < -E.toSemi.nInf
  omega

theorem imbalance_plusStepLow_lt
    (E : LowDegree (K := K))
    (hn : 0 ≤ E.toSemi.nInf)
    (hhigh : 2 <
      (E.toSemi.u.natDegree : ℤ) + E.toSemi.nInf) :
    imbalance (plusStepLow E) < imbalance E := by
  have hnewLower := plusStep_lower_wall E hhigh
  have hexcess := plusStep_upper_excess_lt E
  have holdLower :
      lowerDefect E = 0 := by
    rw [lowerDefect, Int.toNat_eq_zero]
    omega
  have hnextLower :
      lowerDefect (plusStepLow E) = 0 := by
    rw [lowerDefect, Int.toNat_eq_zero]
    exact neg_nonpos.mpr hnewLower
  rw [imbalance, imbalance, holdLower, hnextLower,
    Nat.zero_add, Nat.zero_add]
  apply (Int.toNat_lt_toNat (by omega)).2
  exact hexcess

/-! ## Structural infinity balancing -/

def toBalanced
    (E : LowDegree (K := K))
    (hzero : 0 ≤ E.toSemi.nInf)
    (hupper :
      (E.toSemi.u.natDegree : ℤ) + E.toSemi.nInf ≤ 2) :
    N13Mumford.Mumford K where
  u := E.toSemi.u
  v := E.toSemi.v
  nInf := Int.toNat E.toSemi.nInf
  u_monic := E.toSemi.u_monic
  deg_u := E.degree_le_two
  v_reduced := E.toSemi.v_reduced
  curve_dvd := E.toSemi.curve_dvd
  infinity_bound := by
    have hn :
        ((Int.toNat E.toSemi.nInf : ℕ) : ℤ) =
          E.toSemi.nInf :=
      Int.toNat_of_nonneg hzero
    omega

@[simp] theorem toBalanced_toSemi
    (E : LowDegree (K := K))
    (hzero : 0 ≤ E.toSemi.nInf)
    (hupper :
      (E.toSemi.u.natDegree : ℤ) + E.toSemi.nInf ≤ 2) :
    (toBalanced E hzero hupper).toSemi = E.toSemi := by
  cases E with
  | mk D hdeg =>
      cases D with
      | mk u v n hu hv hc =>
          simp only [toBalanced, Mumford.toSemi]
          congr
          exact Int.toNat_of_nonneg hzero

def balanceInfinity
    (E : LowDegree (K := K)) :
    N13Mumford.Mumford K :=
  if hn : E.toSemi.nInf < 0 then
    balanceInfinity (minusStepLow E)
  else if hhigh :
      2 < (E.toSemi.u.natDegree : ℤ) + E.toSemi.nInf then
    balanceInfinity (plusStepLow E)
  else
    toBalanced E (le_of_not_gt hn) (le_of_not_gt hhigh)
termination_by imbalance E
decreasing_by
  · exact imbalance_minusStepLow_lt E hn
  · exact imbalance_plusStepLow_lt E (le_of_not_gt hn) hhigh

theorem balanceInfinity_class
    (E : LowDegree (K := K)) :
    semiMumfordClass (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K)
        (balanceInfinity E).toSemi =
      semiMumfordClass (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K) E.toSemi := by
  fun_induction balanceInfinity E with
  | case1 E hn ih =>
      exact ih.trans (minusStep_class E.toSemi)
  | case2 E hn hhigh ih =>
      exact ih.trans (plusStep_class E.toSemi)
  | case3 E hn hhigh =>
      rw [toBalanced_toSemi]

def normalizeSemi
    (D₀ : N13Mumford.SemiMumford K) :
    N13Mumford.Mumford K :=
  balanceInfinity
    (reduceDegree (N13Mumford.model K)
      (N13Infinity.positiveInfinityOrder K) D₀)

theorem normalizeSemi_class
    (D₀ : N13Mumford.SemiMumford K) :
    semiMumfordClass (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K)
        (normalizeSemi D₀).toSemi =
      semiMumfordClass (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K) D₀ := by
  exact
    (balanceInfinity_class
      (reduceDegree (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K) D₀)).trans
      (reduceDegree_class (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K) D₀)

theorem classOf_surjective :
    Function.Surjective
      (classOf (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K)) := by
  intro c
  obtain ⟨E, hE⟩ :=
    exists_lowDegreeSemiRepresentative
      (N13Mumford.model K)
      (N13Infinity.positiveInfinityOrder K) c
  refine ⟨balanceInfinity E, ?_⟩
  rw [← semiMumfordClass_toSemi]
  exact (balanceInfinity_class E).trans hE

end

end MazurProof.N13MumfordInfinityBalance


