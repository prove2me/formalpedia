-- Prove2me | Definitions.Def_MazurN13_p05
-- name    : MazurN13_p05
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-08T00:14:45.173984+00:00
-- url     : https://prove2.me/theorems/d23b1e1a-1b8c-4d7b-9776-2fbf97989b83
-- title:
--   Mazur order 13 (Huang FLT port), part 5/33
-- statement:
--   Part 5 of 33 of a machine-checked Lean proof that no elliptic curve over $\mathbb{Q}$ has a rational point of exact order $13$ (the case $N=13$ of Mazur's torsion theorem). The chain as a whole proves that the only rational affine points of the genus-two curve $Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$ (a model of $X_1(13)$) have $X\in\{0,-1\}$ (cusps); the final result is `MazurProof.N13ConstructedRationalPointTheorem.affine_x_is_cuspidal` in part {N}.
--
--   This part is not a single definition: it is a verbatim, sorry-free slice of Xiang Huang's Lean development, ported to this Mathlib and split into compile-sized pieces, each importing the previous part. It contains the modules:
--
--   - `FLT.Assumptions.MazurProof.N13MumfordInfinityBalance`
--   - `FLT.Assumptions.MazurProof.N13SmallMumfordRigidity`
--   - `FLT.Assumptions.MazurProof.N13TwoAdicAbelChartPic`
--   - `FLT.Assumptions.MazurProof.N13TwoAdicAbelChartRecover`
--   - `FLT.Assumptions.MazurProof.N13AbelCompatibleGraphRecover`
--   - `FLT.Assumptions.MazurProof.N13RankTwoQuotientAlgebra`
--   - `FLT.Assumptions.MazurProof.N13RankTwoIdealRecovery`
--   - `FLT.Assumptions.MazurProof.N13QuotientReduction`
--   - `FLT.Assumptions.MazurProof.SexticMumfordQuotientBasis`
--   - `FLT.Assumptions.MazurProof.N13CanonicalContractionQuotient`
--   - `FLT.Assumptions.MazurProof.N13QuotientVerticalFlatness`
--   - `FLT.Assumptions.MazurProof.N13TensorSpecialFiber`
--   - `FLT.Assumptions.MazurProof.N13TwoFiberNoEscape`
--
--   Port notes: API drift fixes only (transparency options, renamed lemmas, explicit instances); local notations expanded, `private` removed.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT commit 51bbb4f, directory FLT/Assumptions/MazurProof (N13* and SexticMumford* modules and their dependencies)

import Mathlib
import Definitions.Def_MazurN13_p04
set_option maxHeartbeats 1000000

-- module FLT.Assumptions.MazurProof.N13MumfordInfinityBalance
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MumfordInfinityBalance =====
section

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
theorem sub_mod_dvd
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

theorem curve_dvd_of_congr
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

theorem mod_natDegree_lt
    (p : K[X]) (hpos : 0 < D.u.natDegree) :
    (p % D.u).natDegree < D.u.natDegree := by
  by_cases hr : p % D.u = 0
  · rw [hr]
    simp
    exact hpos
  · exact natDegree_lt_natDegree hr
      (degree_mod_lt p D.u_monic.ne_zero)

theorem mod_eq_zero_of_natDegree_eq_zero
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

theorem two_mul_sqrt_mul_natDegree_le
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
theorem remainder_sq_natDegree_le
    (r : K[X]) {d : ℕ} (hd : d ≤ 2) (hr : r.natDegree < d) :
    (r ^ 2).natDegree ≤ d + 2 := by
  rw [natDegree_pow]
  omega

theorem adaptedNumerator_natDegree_le
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

theorem adaptedNumeratorNeg_natDegree_le
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
theorem evalPoly_coeff_neg_three_eq_zero
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
theorem evalSqrtInfinity_coeff_neg_three :
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

theorem wSeries_coeff_zero :
    (N13Infinity.wSeries K).coeff (0 : ℤ) = 1 := by
  change (HahnSeries.ofPowerSeries ℤ K
    (N13Infinity.sqrtReverseF K)).coeff (0 : ℕ) = 1
  rw [HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff,
    N13Infinity.sqrtReverseF_constantCoeff]

theorem ySeries_coeff_neg_three :
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

theorem linearFunction_neg_eq_ySubClass
    (V : K[X]) :
    N13BranchNorm.linearFunction K (-V) 1 =
      ySubClass (N13Mumford.model K) V := by
  simp [N13BranchNorm.linearFunction, ySubClass]
  ring

theorem branch_order_lower_bounds_of_natDegree_three
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
  rw [plusStep, cantorNextSemi_nInf, plusCorrection_order D hdeg]
  ring

@[simp] theorem minusStep_nInf
    (hdeg : D.u.natDegree ≤ 2) :
    (minusStep D).nInf =
      D.nInf + 3 - (minusFactor D).natDegree := by
  rw [minusStep, cantorNextSemi_nInf, minusCorrection_order D hdeg]
  ring

@[simp] theorem plusStep_natDegree :
    (plusStep D).u.natDegree = (plusFactor D).natDegree := by
  rw [plusStep, cantorNextSemi_natDegree]

@[simp] theorem minusStep_natDegree :
    (minusStep D).u.natDegree = (minusFactor D).natDegree := by
  rw [minusStep, cantorNextSemi_natDegree]

theorem adaptedBezout
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

end
end

-- module FLT.Assumptions.MazurProof.N13SmallMumfordRigidity
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SmallMumfordRigidity =====
section

/-!
# Rigidity of balanced Mumford representatives on `X₁(13)`

For balanced representatives, a principal relation clears to two affine
factors whose product has degree at most four.  The two-infinity pole-order
argument forces both factors into the polynomial subring.  Ideal
contraction then identifies the monic `u`-polynomials, so the principal
function is constant and the balanced representatives agree.

Together with structural infinity balancing, this gives the full unique
Mumford normal form and hence the Abel--Jacobi embedding of the curve,
without coefficient enumeration.
-/

open Polynomial
open scoped LaurentSeries nonZeroDivisors

namespace MazurProof.N13SmallMumfordRigidity

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

open SexticMumford

theorem numerator_order
    (α : (N13Mumford.FunctionField K)ˣ)
    (u : K[X]) (z : N13Mumford.CoordinateRing K)
    (hu : u ≠ 0)
    (hz :
      algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) z =
        (α : N13Mumford.FunctionField K) *
          algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K)
            (xClass (N13Mumford.model K) u)) :
    (N13Infinity.coordinateToLaurent K z).order =
      (N13Infinity.functionFieldToLaurent K
          (α : N13Mumford.FunctionField K)).order -
        (u.natDegree : ℤ) := by
  have hα :
      N13Infinity.functionFieldToLaurent K
          (α : N13Mumford.FunctionField K) ≠ 0 :=
    by simpa only [map_zero] using
      (N13Infinity.functionFieldToLaurent_injective K).ne α.ne_zero
  have huL : N13BranchNorm.evalPoly K u ≠ 0 :=
    N13BranchNorm.evalPoly_ne_zero K hu
  have hmapped := congrArg (N13Infinity.functionFieldToLaurent K) hz
  rw [map_mul, N13Infinity.functionFieldToLaurent_algebraMap,
    N13Infinity.functionFieldToLaurent_algebraMap,
    N13Infinity.coordinateToLaurent_xClass] at hmapped
  change
    N13Infinity.coordinateToLaurent K z =
      N13Infinity.functionFieldToLaurent K
          (α : N13Mumford.FunctionField K) *
        N13BranchNorm.evalPoly K u at hmapped
  calc
    (N13Infinity.coordinateToLaurent K z).order =
        (N13Infinity.functionFieldToLaurent K
            (α : N13Mumford.FunctionField K) *
          N13BranchNorm.evalPoly K u).order := by rw [hmapped]
    _ =
        (N13Infinity.functionFieldToLaurent K
            (α : N13Mumford.FunctionField K)).order +
          (N13BranchNorm.evalPoly K u).order :=
      HahnSeries.order_mul hα huL
    _ = _ := by
      rw [N13BranchNorm.evalPoly_order K u hu]
      omega

theorem inverse_order
    (α : (N13Mumford.FunctionField K)ˣ) :
    (N13Infinity.functionFieldToLaurent K
        (↑α⁻¹ : N13Mumford.FunctionField K)).order =
      -(N13Infinity.functionFieldToLaurent K
        (α : N13Mumford.FunctionField K)).order := by
  let a :=
    N13Infinity.functionFieldToLaurent K
      (α : N13Mumford.FunctionField K)
  let b :=
    N13Infinity.functionFieldToLaurent K
      (↑α⁻¹ : N13Mumford.FunctionField K)
  have ha : a ≠ 0 :=
    by simpa only [a, map_zero] using
      (N13Infinity.functionFieldToLaurent_injective K).ne α.ne_zero
  have hb : b ≠ 0 := by
    simpa only [b, map_zero] using
      (N13Infinity.functionFieldToLaurent_injective K).ne
        (Units.ne_zero α⁻¹)
  have hab : a * b = 1 := by
    simp [a, b]
  have hord := HahnSeries.order_mul ha hb
  rw [hab, HahnSeries.order_one] at hord
  change b.order = -a.order
  omega

theorem orientation_order
    (D₁ D₂ : Mumford (N13Mumford.model K))
    (α : (N13Mumford.FunctionField K)ˣ)
    (hInf :
      Multiplicative.ofAdd ((D₁.nInf : ℤ) - 1) *
          (N13Infinity.positiveInfinityOrder K).ordPlus α =
        Multiplicative.ofAdd ((D₂.nInf : ℤ) - 1)) :
    (N13Infinity.functionFieldToLaurent K
        (α : N13Mumford.FunctionField K)).order =
      (D₂.nInf : ℤ) - D₁.nInf := by
  change
    Multiplicative.ofAdd
        (((D₁.nInf : ℤ) - 1) +
          (N13Infinity.functionFieldToLaurent K
            (α : N13Mumford.FunctionField K)).order) =
      Multiplicative.ofAdd ((D₂.nInf : ℤ) - 1) at hInf
  have h := Multiplicative.ofAdd.injective hInf
  omega

theorem principal_is_constant
    (D₁ D₂ : Mumford (N13Mumford.model K))
    (α : (N13Mumford.FunctionField K)ˣ)
    (hIdeal :
      mumfordIdealUnit (N13Mumford.model K) D₁.toSemi *
          toPrincipalIdeal (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) α =
        mumfordIdealUnit (N13Mumford.model K) D₂.toSemi)
    (hInf :
      Multiplicative.ofAdd ((D₁.nInf : ℤ) - 1) *
          (N13Infinity.positiveInfinityOrder K).ordPlus α =
        Multiplicative.ofAdd ((D₂.nInf : ℤ) - 1)) :
    ∃ c : Kˣ, α = N13Infinity.functionConstUnit K c := by
  let M := N13Mumford.model K
  obtain ⟨z, w, hzmem, hwmem, hprod, hzeq, hweq⟩ :=
    exists_integral_factor_pair_of_principal_relation
      M D₁.toSemi D₂.toSemi α hIdeal
  change z ∈ mumfordIdeal M D₂.u D₂.v at hzmem
  change w ∈ mumfordIdeal M D₁.u D₁.v at hwmem
  change z * w = xClass M (D₁.u * D₂.u) at hprod
  change
    algebraMap (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K) z =
      (α : N13Mumford.FunctionField K) *
        algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) (xClass M D₁.u) at hzeq
  change
    algebraMap (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K) w =
      (↑α⁻¹ : N13Mumford.FunctionField K) *
        algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) (xClass M D₂.u) at hweq
  have hu₁ : D₁.u ≠ 0 := D₁.u_monic.ne_zero
  have hu₂ : D₂.u ≠ 0 := D₂.u_monic.ne_zero
  have hαorder := orientation_order K D₁ D₂ α hInf
  have hzorder := numerator_order K α D₁.u z hu₁ hzeq
  have hworder := numerator_order K α⁻¹ D₂.u w hu₂ hweq
  have hαinv := inverse_order K α
  have hzplus :
      (-2 : ℤ) ≤ (N13Infinity.coordinateToLaurent K z).order := by
    rw [hzorder, hαorder]
    have hbound := D₁.infinity_bound
    omega
  have hwplus :
      (-2 : ℤ) ≤ (N13Infinity.coordinateToLaurent K w).order := by
    rw [hworder, hαinv, hαorder]
    have hbound := D₂.infinity_bound
    omega
  have hP : D₁.u * D₂.u ≠ 0 := mul_ne_zero hu₁ hu₂
  have hPdeg : (D₁.u * D₂.u).natDegree ≤ 4 := by
    rw [Polynomial.natDegree_mul hu₁ hu₂]
    have hdeg₁ := D₁.deg_u
    have hdeg₂ := D₂.deg_u
    omega
  obtain ⟨hzY, hwY⟩ :=
    N13FactorRigidity.factor_pair_coeffY_eq_zero K z w
      (D₁.u * D₂.u) hP hPdeg hprod hzplus hwplus
  let pz := coeff0 M z
  let pw := coeff0 M w
  have hzpoly : z = xClass M pz := by
    have hzY' : coeffY M z = 0 := by simpa [M] using hzY
    rw [← recompose M z]
    rw [hzY']
    simp [pz]
  have hwpoly : w = xClass M pw := by
    have hwY' : coeffY M w = 0 := by simpa [M] using hwY
    rw [← recompose M w]
    rw [hwY']
    simp [pw]
  have hpoly : pz * pw = D₁.u * D₂.u := by
    apply xClass_injective M
    rw [xClass_mul, ← hzpoly, ← hwpoly, hprod]
  have hu₂pz : D₂.u ∣ pz := by
    have hm :
        pz ∈
          (mumfordIdeal M D₂.u D₂.v).comap (xClassHom M) := by
      change xClass M pz ∈ mumfordIdeal M D₂.u D₂.v
      rw [← hzpoly]
      exact hzmem
    have hbase :
        (mumfordIdeal M D₂.u D₂.v).comap (xClassHom M) =
          Ideal.span ({D₂.u} : Set K[X]) := by
      simpa only [toSemi_u, toSemi_v] using
        mumfordIdeal_comap_base M D₂.toSemi
    rw [hbase, Ideal.mem_span_singleton] at hm
    exact hm
  have hu₁pw : D₁.u ∣ pw := by
    have hm :
        pw ∈
          (mumfordIdeal M D₁.u D₁.v).comap (xClassHom M) := by
      change xClass M pw ∈ mumfordIdeal M D₁.u D₁.v
      rw [← hwpoly]
      exact hwmem
    have hbase :
        (mumfordIdeal M D₁.u D₁.v).comap (xClassHom M) =
          Ideal.span ({D₁.u} : Set K[X]) := by
      simpa only [toSemi_u, toSemi_v] using
        mumfordIdeal_comap_base M D₁.toSemi
    rw [hbase, Ideal.mem_span_singleton] at hm
    exact hm
  obtain ⟨c, hpc⟩ := hu₂pz
  obtain ⟨d, hpd⟩ := hu₁pw
  have hcd : c * d = 1 := by
    apply mul_left_cancel₀ hP
    calc
      (D₁.u * D₂.u) * (c * d) =
          (D₂.u * c) * (D₁.u * d) := by ring
      _ = pz * pw := by rw [← hpc, ← hpd]
      _ = D₁.u * D₂.u := hpoly
      _ = (D₁.u * D₂.u) * 1 := by rw [mul_one]
  have hcunit : IsUnit c :=
    isUnit_iff_exists_inv.mpr ⟨d, hcd⟩
  have hpzfield :
      algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) (xClass M pz) =
        (α : N13Mumford.FunctionField K) *
          algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) (xClass M D₁.u) := by
    rw [← hzpoly]
    exact hzeq
  have hscale :
      (α : N13Mumford.FunctionField K) *
          algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) (xClass M D₁.u) =
        algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) (xClass M D₂.u) *
          algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) (xClass M c) := by
    calc
      _ = algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) (xClass M pz) :=
        hpzfield.symm
      _ = algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) (xClass M (D₂.u * c)) := by
            rw [hpc]
      _ = _ := by rw [xClass_mul, map_mul]
  have hunitX : xClass M c * xClass M d = 1 := by
    rw [← xClass_mul, hcd, xClass_one]
  have huEq : D₁.u = D₂.u :=
    mumford_u_eq_of_principal_scale M D₁.toSemi D₂.toSemi α
      (xClass M c) (xClass M d) hIdeal hscale hunitX
  have hpc' : pz = D₁.u * c := by
    rw [huEq]
    exact hpc
  have huField :
      algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) (xClass M D₁.u) ≠ 0 := by
    simpa using
      (IsFractionRing.injective
        (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)).ne
        (xClass_ne_zero M hu₁)
  have hαfield :
      (α : N13Mumford.FunctionField K) =
        algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) (xClass M c) := by
    apply mul_right_cancel₀ huField
    calc
      (α : N13Mumford.FunctionField K) *
            algebraMap (N13Mumford.CoordinateRing K)
              (N13Mumford.FunctionField K) (xClass M D₁.u) =
          algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) (xClass M pz) :=
        hpzfield.symm
      _ = algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K)
            (xClass M (D₁.u * c)) := by rw [hpc']
      _ = algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K)
            (xClass M D₁.u * xClass M c) := by rw [xClass_mul]
      _ = algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) (xClass M c) *
          algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) (xClass M D₁.u) := by
              rw [map_mul]
              ring
  obtain ⟨r, hrunit, hCr⟩ := Polynomial.isUnit_iff.mp hcunit
  let cr : Kˣ := hrunit.unit
  refine ⟨cr, ?_⟩
  apply Units.ext
  change
    (α : N13Mumford.FunctionField K) =
      algebraMap (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)
        (algebraMap K (N13Mumford.CoordinateRing K) (cr : K))
  rw [hαfield, ← hCr]
  rfl

theorem eq_of_class_eq
    (D₁ D₂ : Mumford (N13Mumford.model K))
    (hclass :
      classOf (N13Mumford.model K)
          (N13Infinity.positiveInfinityOrder K) D₁ =
        classOf (N13Mumford.model K)
          (N13Infinity.positiveInfinityOrder K) D₂) :
    D₁ = D₂ := by
  obtain ⟨α, hIdeal, hInf⟩ :=
    (classOf_eq_iff (N13Mumford.model K)
      (N13Infinity.positiveInfinityOrder K) D₁ D₂).mp hclass
  obtain ⟨c, hα⟩ :=
    principal_is_constant K D₁ D₂ α hIdeal hInf
  exact N13Mumford.principal_between_balanced_of_constant
    K c hα hIdeal hInf

theorem eq_of_class_eq_of_small
    (D₁ D₂ : Mumford (N13Mumford.model K))
    (_hsmall₁ : D₁.u.natDegree + D₁.nInf ≤ 1)
    (_hsmall₂ : D₂.u.natDegree + D₂.nInf ≤ 1)
    (hclass :
      classOf (N13Mumford.model K)
          (N13Infinity.positiveInfinityOrder K) D₁ =
        classOf (N13Mumford.model K)
          (N13Infinity.positiveInfinityOrder K) D₂) :
    D₁ = D₂ :=
  eq_of_class_eq K D₁ D₂ hclass

theorem classOf_injective :
    Function.Injective
      (classOf (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K)) := by
  intro D₁ D₂
  exact eq_of_class_eq K D₁ D₂

theorem existsUnique_classOf
    (c : ConcretePic (N13Mumford.model K)
      (N13Infinity.positiveInfinityOrder K)) :
    ∃! D : Mumford (N13Mumford.model K),
      classOf (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K) D = c := by
  obtain ⟨D, hD⟩ :=
    N13MumfordInfinityBalance.classOf_surjective c
  refine ⟨D, hD, ?_⟩
  intro E hE
  exact classOf_injective K (hE.trans hD.symm)

instance instNormalFormData :
    NormalFormData (N13Mumford.model K)
      (N13Infinity.positiveInfinityOrder K) where
  existsUnique := existsUnique_classOf K

theorem pointMumford_small
    (P : CurvePoint (N13Mumford.model K)) :
    (pointMumford (N13Mumford.model K) P).u.natDegree +
        (pointMumford (N13Mumford.model K) P).nInf ≤ 1 := by
  cases P with
  | infinityPlus =>
      simp [pointMumford, zero]
  | infinityMinus =>
      simp [pointMumford, infinityMinusMumford]
  | affine x y h =>
      simp [pointMumford, affinePointMumford]

theorem point_class_injective :
    Function.Injective
      (fun P : CurvePoint (N13Mumford.model K) =>
        classOf (N13Mumford.model K)
          (N13Infinity.positiveInfinityOrder K)
          (pointMumford (N13Mumford.model K) P)) := by
  intro P Q hPQ
  apply pointMumford_injective (N13Mumford.model K)
  exact eq_of_class_eq_of_small K _ _
    (pointMumford_small K P) (pointMumford_small K Q) hPQ

end

end MazurProof.N13SmallMumfordRigidity

end
end

-- module FLT.Assumptions.MazurProof.N13TwoAdicAbelChartPic
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoAdicAbelChartPic =====
section

/-!
# The N13 two-adic Abel chart inside the oriented Picard group

Every pair in the two distinguished residue disks gives smooth integral
generalized Mumford data.  After extending coefficients and completing the
square, the resulting standard sextic semirepresentative already has degree
two and infinity balance zero.  It is therefore a balanced Mumford
representative over `ℚ₂`.

Unique balanced normal forms make the resulting map to the oriented Picard
group injective.  Translating by the distinguished base pair gives the
faithful chart centred at the identity.  Thus the remaining geometric input
for the formal-kernel argument is existence of representatives in this
chart, not their uniqueness.
-/

open Polynomial

namespace MazurProof.N13TwoAdicAbelChartPic

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev Q₂ : Type :=
  ℚ_[2]

abbrev DiskPair : Type :=
  N13TwoAdicAbelChartData.DiskPair

abbrev Pic : Type :=
  SexticMumford.ConcretePic
    (N13Mumford.model Q₂)
    (N13Infinity.positiveInfinityOrder Q₂)

namespace DiskPair

variable (P : DiskPair)

theorem u_natDegree :
    P.u.natDegree = 2 := by
  rw [N13TwoAdicAbelChartData.DiskPair.u,
    Polynomial.natDegree_mul
      (monic_X_sub_C P.x₀).ne_zero
      (monic_X_sub_C P.x₁).ne_zero]
  simp

theorem sexticSemi_u_natDegree :
    (N13TwoAdicMumfordTransport.sexticSemi
      P.smoothMumford 0).u.natDegree = 2 := by
  rw [N13TwoAdicMumfordTransport.sexticSemi_u,
    N13TwoAdicAbelChartData.DiskPair.smoothMumford_u,
    N13TwoAdicMumfordTransport.mapPoly_apply,
    P.u_monic.natDegree_map]
  exact P.u_natDegree

/-- The standard sextic representative of a two-disk divisor is already
balanced: its affine degree is two and its infinity multiplicity is zero. -/
def mumford :
    N13Mumford.Mumford Q₂ := by
  let D :=
    N13TwoAdicMumfordTransport.sexticSemi
      P.smoothMumford 0
  exact
    { u := D.u
      v := D.v
      nInf := 0
      u_monic := D.u_monic
      deg_u := by
        rw [P.sexticSemi_u_natDegree]
      v_reduced := D.v_reduced
      curve_dvd := D.curve_dvd
      infinity_bound := by
        rw [P.sexticSemi_u_natDegree] }

@[simp] theorem mumford_u :
    P.mumford.u =
      N13TwoAdicMumfordTransport.mapPoly P.u := rfl

@[simp] theorem mumford_v :
    P.mumford.v =
      (N13TwoAdicMumfordTransport.sexticSemi
        P.smoothMumford 0).v := rfl

@[simp] theorem mumford_nInf :
    P.mumford.nInf = 0 := rfl

/-- The oriented Picard class of the two-disk divisor. -/
def pic : Pic :=
  SexticMumford.classOf
    (N13Mumford.model Q₂)
    (N13Infinity.positiveInfinityOrder Q₂)
    P.mumford

/-- Distinct pairs in the two residue disks give distinct Picard classes.
The proof is global normal-form rigidity followed by faithfulness of
coefficient extension. -/
theorem pic_injective :
    Function.Injective DiskPair.pic := by
  intro P Q hPQ
  have hM : P.mumford = Q.mumford :=
    N13SmallMumfordRigidity.classOf_injective Q₂ hPQ
  apply N13TwoAdicAbelChartData.DiskPair.u_injective
  apply Polynomial.map_injective
    N13TwoAdicMumfordTransport.coeffMap
    (IsFractionRing.injective
      N13TwoAdicMumfordTransport.R₂ Q₂)
  simpa only [mumford_u,
    N13TwoAdicMumfordTransport.mapPoly_apply] using
    congrArg SexticMumford.Mumford.u hM

/-- Translate the chart so that the distinguished divisor is the identity. -/
def centeredPic : DiskPair → Pic :=
  fun P => P.pic -
    pic N13TwoAdicAbelChartData.basePair

@[simp] theorem centeredPic_basePair :
    centeredPic N13TwoAdicAbelChartData.basePair = 0 := by
  simp [centeredPic]

theorem centeredPic_injective :
    Function.Injective centeredPic := by
  intro P Q hPQ
  apply pic_injective
  exact sub_left_injective hPQ

end DiskPair

end

end MazurProof.N13TwoAdicAbelChartPic

end
end

-- module FLT.Assumptions.MazurProof.N13TwoAdicAbelChartRecover
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoAdicAbelChartRecover =====
section

/-!
# Recovering the N13 two-disk divisor from an integral Mumford graph

Suppose a smooth integral generalized Mumford graph reduces to the fixed
nonspecial graph `(X² + X, 0)`.  Hensel lifting splits its monic quadratic
into one root in each of the residue disks of `0` and `-1`.  Evaluating the
curve relation at those roots and using uniqueness in the vertical Hensel
fibres identifies the graph values with the canonical disk lifts.

Consequently every such integral graph comes from a unique `DiskPair`, up
to the harmless operation of changing its graph polynomial by a multiple
of `u`.  This is the algebraic reverse of
`N13TwoAdicAbelChartData.DiskPair.smoothMumford`; no divisor enumeration or
properness shortcut is used.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13TwoAdicAbelChartRecover

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  ℤ_[2]

abbrev K : Type :=
  N13GoodCoordinateRingTwo.K

abbrev Q₂ : Type :=
  ℚ_[2]

abbrev Pic : Type :=
  N13TwoAdicAbelChartPic.Pic

abbrev maximal : Ideal R₂ :=
  IsLocalRing.maximalIdeal R₂

set_option maxHeartbeats 4000000 in
attribute [local irreducible] MazurProof.SexticMumford.curvePoly in
/-- Smooth integral Mumford data whose graph has the selected nonspecial
special fibre. -/
structure NearBaseMumford
    extends N13GeneralizedMumfordReduction.SmoothMumford₂ where
  reduce_u :
    N13GeneralizedMumfordReduction.reducePoly u =
      (X ^ 2 + X : K[X])
  reduce_v :
    N13GeneralizedMumfordReduction.reducePoly v = 0

namespace NearBaseMumford

variable (D : NearBaseMumford)

/-- Every two-disk divisor gives near-base integral data. -/
def ofDiskPair
    (P : N13TwoAdicAbelChartData.DiskPair) :
    NearBaseMumford where
  toSmoothMumford₂ := P.smoothMumford
  reduce_u := P.reducePoly_u
  reduce_v := P.reducePoly_v

@[simp] theorem ofDiskPair_u
    (P : N13TwoAdicAbelChartData.DiskPair) :
    (ofDiskPair P).u = P.u := rfl

@[simp] theorem ofDiskPair_v
    (P : N13TwoAdicAbelChartData.DiskPair) :
    (ofDiskPair P).v = P.v := rfl

theorem mem_maximal_iff_reduceBase_eq_zero
    (a : R₂) :
    a ∈ maximal ↔
      N13GeneralizedMumfordReduction.reduceBase a = 0 := by
  constructor
  · intro ha
    have hker :
        a ∈ RingHom.ker (PadicInt.toZMod : R₂ →+* K) := by
      rw [PadicInt.ker_toZMod]
      exact ha
    exact RingHom.mem_ker.mp hker
  · intro ha
    have hker :
        a ∈ RingHom.ker (PadicInt.toZMod : R₂ →+* K) :=
      RingHom.mem_ker.mpr ha
    rw [PadicInt.ker_toZMod] at hker
    exact hker

theorem isUnit_of_reduceBase_eq_one
    {a : R₂}
    (ha :
      N13GeneralizedMumfordReduction.reduceBase a = 1) :
    IsUnit a := by
  apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal isUnit_one
  apply (mem_maximal_iff_reduceBase_eq_zero (a - 1)).2
  rw [map_sub, ha, map_one, sub_self]

theorem reduceBase_eval
    (p : R₂[X]) (a : R₂) :
    N13GeneralizedMumfordReduction.reduceBase (p.eval a) =
      (N13GeneralizedMumfordReduction.reducePoly p).eval
        (N13GeneralizedMumfordReduction.reduceBase a) := by
  rw [N13GeneralizedMumfordReduction.reducePoly_apply,
    Polynomial.eval_map_apply]

theorem reduceBase_derivative_eval
    (p : R₂[X]) (a : R₂) :
    N13GeneralizedMumfordReduction.reduceBase
        (p.derivative.eval a) =
      (N13GeneralizedMumfordReduction.reducePoly p).derivative.eval
        (N13GeneralizedMumfordReduction.reduceBase a) := by
  rw [N13GeneralizedMumfordReduction.reducePoly_apply,
    Polynomial.derivative_map, Polynomial.eval_map_apply]

theorem u_eval_zero_mem :
    D.u.eval 0 ∈ maximal := by
  apply (mem_maximal_iff_reduceBase_eq_zero _).2
  rw [reduceBase_eval, D.reduce_u]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  norm_num [N13GeneralizedMumfordReduction.reduceBase, htwo]

theorem u_eval_negOne_mem :
    D.u.eval (-1) ∈ maximal := by
  apply (mem_maximal_iff_reduceBase_eq_zero _).2
  rw [reduceBase_eval, D.reduce_u]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  norm_num [N13GeneralizedMumfordReduction.reduceBase, htwo]
  exact htwo

theorem derivative_eval_zero_isUnit :
    IsUnit (D.u.derivative.eval 0) := by
  apply isUnit_of_reduceBase_eq_one
  rw [reduceBase_derivative_eval, D.reduce_u]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  norm_num [N13GeneralizedMumfordReduction.reduceBase, htwo]

theorem derivative_eval_negOne_isUnit :
    IsUnit (D.u.derivative.eval (-1)) := by
  apply isUnit_of_reduceBase_eq_one
  rw [reduceBase_derivative_eval, D.reduce_u]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  norm_num [N13GeneralizedMumfordReduction.reduceBase, htwo]
  linear_combination htwo

/-- The root of `u` in the residue disk of zero. -/
theorem exists_root_zeroDisk :
    ∃ x : R₂, D.u.eval x = 0 ∧ x ∈ maximal := by
  obtain ⟨x, hx, hxmem⟩ :=
    HenselianRing.is_henselian
      D.u D.u_monic 0 D.u_eval_zero_mem
      (D.derivative_eval_zero_isUnit.map
        (Ideal.Quotient.mk maximal))
  refine ⟨x, ?_, by simpa using hxmem⟩
  exact hx

/-- The root of `u` in the residue disk of `-1`. -/
theorem exists_root_negOneDisk :
    ∃ x : R₂, D.u.eval x = 0 ∧ x + 1 ∈ maximal := by
  obtain ⟨x, hx, hxmem⟩ :=
    HenselianRing.is_henselian
      D.u D.u_monic (-1) D.u_eval_negOne_mem
      (D.derivative_eval_negOne_isUnit.map
        (Ideal.Quotient.mk maximal))
  refine ⟨x, ?_, by simpa using hxmem⟩
  exact hx

/-- The two Hensel roots, selected in their distinct residue disks. -/
def x₀ : R₂ :=
  Classical.choose D.exists_root_zeroDisk

def x₁ : R₂ :=
  Classical.choose D.exists_root_negOneDisk

theorem x₀_spec :
    D.u.eval D.x₀ = 0 ∧ D.x₀ ∈ maximal :=
  Classical.choose_spec D.exists_root_zeroDisk

theorem x₁_spec :
    D.u.eval D.x₁ = 0 ∧ D.x₁ + 1 ∈ maximal :=
  Classical.choose_spec D.exists_root_negOneDisk

/-- The disk pair cut out by the two Hensel factors of `u`. -/
def diskPair :
    N13TwoAdicAbelChartData.DiskPair where
  x₀ := D.x₀
  x₁ := D.x₁
  x₀_mem := D.x₀_spec.2
  x₁_add_one_mem := D.x₁_spec.2

@[simp] theorem diskPair_x₀ :
    D.diskPair.x₀ = D.x₀ := rfl

@[simp] theorem diskPair_x₁ :
    D.diskPair.x₁ = D.x₁ := rfl

theorem u_natDegree :
    D.u.natDegree = 2 := by
  calc
    D.u.natDegree =
        (D.u.map
          N13GeneralizedMumfordReduction.reduceBase).natDegree :=
      (D.u_monic.natDegree_map
        N13GeneralizedMumfordReduction.reduceBase).symm
    _ =
        (N13GeneralizedMumfordReduction.reducePoly D.u).natDegree := rfl
    _ = (X ^ 2 + X : K[X]).natDegree := by rw [D.reduce_u]
    _ = 2 := by
      compute_degree
      norm_num [K, N13GoodCoordinateRingTwo.K,
        N13GoodModelTwo.F2]

theorem diskPair_u_natDegree :
    D.diskPair.u.natDegree = 2 := by
  rw [N13TwoAdicAbelChartData.DiskPair.u,
    Polynomial.natDegree_mul
      (monic_X_sub_C D.diskPair.x₀).ne_zero
      (monic_X_sub_C D.diskPair.x₁).ne_zero]
  simp

theorem diskPair_u_dvd :
    D.diskPair.u ∣ D.u := by
  have h₀ : X - C D.diskPair.x₀ ∣ D.u := by
    rw [dvd_iff_isRoot, IsRoot, D.diskPair_x₀]
    exact D.x₀_spec.1
  have h₁ : X - C D.diskPair.x₁ ∣ D.u := by
    rw [dvd_iff_isRoot, IsRoot, D.diskPair_x₁]
    exact D.x₁_spec.1
  have hprod :=
    (isCoprime_X_sub_C_of_isUnit_sub
      D.diskPair.x₁_sub_x₀_isUnit).mul_dvd h₁ h₀
  simpa [N13TwoAdicAbelChartData.DiskPair.u, mul_comm] using hprod

/-- The recovered disk pair has exactly the original monic quadratic. -/
theorem diskPair_u :
    D.diskPair.u = D.u := by
  exact
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      D.diskPair.u_monic D.u_monic D.diskPair_u_dvd
      (by rw [D.u_natDegree, D.diskPair_u_natDegree])).symm

theorem v_eval_mem_maximal
    (x : R₂) :
    D.v.eval x ∈ maximal := by
  apply (mem_maximal_iff_reduceBase_eq_zero _).2
  rw [reduceBase_eval, D.reduce_v]
  simp

theorem v_eval_on_curve
    {x : R₂} (hx : D.u.eval x = 0) :
    N13GoodModelTwo.AffineEquation x (D.v.eval x) := by
  have h :=
    congrArg (fun p : R₂[X] => p.eval x) D.curve_eq
  simp only [eval_sub, eval_add, eval_pow, eval_mul] at h
  rw [hx, zero_mul] at h
  rw [N13GoodModelTwo.affineEquation_iff_residual]
  simpa [N13GoodModelTwo.affineResidual,
    N13GoodModelTwo.h, N13GoodModelTwo.rhs,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GeneralizedMumfordIntegral.rhsPoly] using h

theorem v_eval_x₀ :
    D.v.eval D.diskPair.x₀ = D.diskPair.y₀ := by
  exact
    N13TwoAdicDisks.y_eq_zeroDiskY
      D.diskPair.x₀ D.diskPair.x₀_mem
      (D.v_eval_on_curve (by
        rw [D.diskPair_x₀]
        exact D.x₀_spec.1))
      (D.v_eval_mem_maximal D.diskPair.x₀)

theorem v_eval_x₁ :
    D.v.eval D.diskPair.x₁ = D.diskPair.y₁ := by
  exact
    N13TwoAdicDisks.y_eq_negOneDiskY
      D.diskPair.x₁ D.diskPair.x₁_add_one_mem
      (D.v_eval_on_curve (by
        rw [D.diskPair_x₁]
        exact D.x₁_spec.1))
      (D.v_eval_mem_maximal D.diskPair.x₁)

/-- The original graph polynomial and the recovered interpolant agree
modulo the recovered quadratic. -/
theorem diskPair_u_dvd_v_sub :
    D.diskPair.u ∣ D.v - D.diskPair.v := by
  have h₀ :
      X - C D.diskPair.x₀ ∣ D.v - D.diskPair.v := by
    rw [dvd_iff_isRoot, IsRoot, eval_sub,
      D.v_eval_x₀,
      N13TwoAdicAbelChartData.DiskPair.v_eval_x₀,
      sub_self]
  have h₁ :
      X - C D.diskPair.x₁ ∣ D.v - D.diskPair.v := by
    rw [dvd_iff_isRoot, IsRoot, eval_sub,
      D.v_eval_x₁,
      N13TwoAdicAbelChartData.DiskPair.v_eval_x₁,
      sub_self]
  have hprod :=
    (isCoprime_X_sub_C_of_isUnit_sub
      D.diskPair.x₁_sub_x₀_isUnit).mul_dvd h₁ h₀
  simpa [N13TwoAdicAbelChartData.DiskPair.u, mul_comm] using hprod

theorem u_dvd_v_sub_diskPair_v :
    D.u ∣ D.v - D.diskPair.v := by
  rw [← D.diskPair_u]
  exact D.diskPair_u_dvd_v_sub

/-- Generalized Mumford graph ideals only depend on `v` modulo `u`. -/
theorem mumfordIdeal_eq_of_dvd_sub
    (u v w : R₂[X]) (hvw : u ∣ v - w) :
    N13GeneralizedMumfordIntegral.mumfordIdeal u v =
      N13GeneralizedMumfordIntegral.mumfordIdeal u w := by
  obtain ⟨q, hq⟩ := hvw
  have hmultiple :
      N13GeneralizedMumfordIntegral.xClass (v - w) =
        N13GeneralizedMumfordIntegral.xClass u *
          N13GeneralizedMumfordIntegral.xClass q := by
    rw [hq, N13GeneralizedMumfordIntegral.xClass_mul]
  have hyw :
      N13GeneralizedMumfordIntegral.ySubClass w =
        N13GeneralizedMumfordIntegral.ySubClass v +
          N13GeneralizedMumfordIntegral.xClass (v - w) := by
    simp [N13GeneralizedMumfordIntegral.ySubClass]
  have hyv :
      N13GeneralizedMumfordIntegral.ySubClass v =
        N13GeneralizedMumfordIntegral.ySubClass w -
          N13GeneralizedMumfordIntegral.xClass (v - w) := by
    rw [hyw]
    ring
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact
        N13GeneralizedMumfordIntegral.xClass_mem_mumfordIdeal u w
    · rw [hyv, hmultiple]
      exact Ideal.sub_mem _
        (N13GeneralizedMumfordIntegral.ySubClass_mem_mumfordIdeal u w)
        (by
          simpa only [mul_comm] using
            Ideal.mul_mem_left
              (N13GeneralizedMumfordIntegral.mumfordIdeal u w)
              (N13GeneralizedMumfordIntegral.xClass q)
              (N13GeneralizedMumfordIntegral.xClass_mem_mumfordIdeal u w))
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact
        N13GeneralizedMumfordIntegral.xClass_mem_mumfordIdeal u v
    · rw [hyw, hmultiple]
      exact Ideal.add_mem _
        (N13GeneralizedMumfordIntegral.ySubClass_mem_mumfordIdeal u v)
        (by
          simpa only [mul_comm] using
            Ideal.mul_mem_left
              (N13GeneralizedMumfordIntegral.mumfordIdeal u v)
              (N13GeneralizedMumfordIntegral.xClass q)
              (N13GeneralizedMumfordIntegral.xClass_mem_mumfordIdeal u v))

/-- The recovered disk pair cuts out exactly the original integral graph
ideal. -/
theorem mumfordIdeal_diskPair :
    N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v =
      N13GeneralizedMumfordIntegral.mumfordIdeal
        D.diskPair.u D.diskPair.v := by
  rw [D.diskPair_u]
  exact mumfordIdeal_eq_of_dvd_sub
    D.u D.v D.diskPair.v D.u_dvd_v_sub_diskPair_v

/-- Completion of the square carries the original graph and the recovered
disk graph to the same standard sextic Mumford ideal. -/
theorem sextic_mumfordIdeal_diskPair :
    SexticMumford.mumfordIdeal
        (N13Mumford.model Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.toSmoothMumford₂ 0).u
        (N13TwoAdicMumfordTransport.sexticSemi
          D.toSmoothMumford₂ 0).v =
      SexticMumford.mumfordIdeal
        (N13Mumford.model Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.diskPair.smoothMumford 0).u
        (N13TwoAdicMumfordTransport.sexticSemi
          D.diskPair.smoothMumford 0).v := by
  rw [
    ← N13TwoAdicCoordinateBaseChange.map_mumfordIdeal_sexticSemi
      D.toSmoothMumford₂ 0,
    ← N13TwoAdicCoordinateBaseChange.map_mumfordIdeal_sexticSemi
      D.diskPair.smoothMumford 0]
  exact congrArg
    (Ideal.map N13TwoAdicCoordinateBaseChange.integralToSextic)
    D.mumfordIdeal_diskPair

theorem sextic_mumfordIdealUnit_diskPair :
    SexticMumford.mumfordIdealUnit
        (N13Mumford.model Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.toSmoothMumford₂ 0) =
      SexticMumford.mumfordIdealUnit
        (N13Mumford.model Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.diskPair.smoothMumford 0) := by
  apply Units.ext
  change
    (SexticMumford.mumfordIdeal
        (N13Mumford.model Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.toSmoothMumford₂ 0).u
        (N13TwoAdicMumfordTransport.sexticSemi
          D.toSmoothMumford₂ 0).v :
      FractionalIdeal
        (N13Mumford.CoordinateRing Q₂)⁰
        (N13Mumford.FunctionField Q₂)) =
      SexticMumford.mumfordIdeal
        (N13Mumford.model Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.diskPair.smoothMumford 0).u
        (N13TwoAdicMumfordTransport.sexticSemi
          D.diskPair.smoothMumford 0).v
  rw [D.sextic_mumfordIdeal_diskPair]

/-- The oriented two-adic Picard class carried by a near-base integral
graph. -/
def pic : Pic :=
  SexticMumford.semiMumfordClass
    (N13Mumford.model Q₂)
    (N13Infinity.positiveInfinityOrder Q₂)
    (N13TwoAdicMumfordTransport.sexticSemi
      D.toSmoothMumford₂ 0)

/-- Recovery is compatible with the actual oriented Picard class. -/
theorem pic_eq_diskPair_pic :
    D.pic =
      N13TwoAdicAbelChartPic.DiskPair.pic D.diskPair := by
  change
    SexticMumford.semiMumfordClass
        (N13Mumford.model Q₂)
        (N13Infinity.positiveInfinityOrder Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.toSmoothMumford₂ 0) =
      SexticMumford.classOf
        (N13Mumford.model Q₂)
        (N13Infinity.positiveInfinityOrder Q₂)
        (N13TwoAdicAbelChartPic.DiskPair.mumford D.diskPair)
  rw [← SexticMumford.semiMumfordClass_toSemi]
  change
    SexticMumford.semiMumfordClass
        (N13Mumford.model Q₂)
        (N13Infinity.positiveInfinityOrder Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.toSmoothMumford₂ 0) =
      SexticMumford.semiMumfordClass
        (N13Mumford.model Q₂)
        (N13Infinity.positiveInfinityOrder Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.diskPair.smoothMumford 0)
  unfold SexticMumford.semiMumfordClass
  congr 2
  apply Prod.ext
  · exact D.sextic_mumfordIdealUnit_diskPair
  · rfl

/-- Centre the integral graph class at the selected base divisor. -/
def centeredPic : Pic :=
  D.pic -
    N13TwoAdicAbelChartPic.DiskPair.pic
      N13TwoAdicAbelChartData.basePair

theorem centeredPic_eq_diskPair_centeredPic :
    D.centeredPic =
      N13TwoAdicAbelChartPic.DiskPair.centeredPic D.diskPair := by
  rw [centeredPic,
    N13TwoAdicAbelChartPic.DiskPair.centeredPic,
    D.pic_eq_diskPair_pic]

@[simp] theorem diskPair_ofDiskPair
    (P : N13TwoAdicAbelChartData.DiskPair) :
    (ofDiskPair P).diskPair = P := by
  apply N13TwoAdicAbelChartData.DiskPair.u_injective
  rw [(ofDiskPair P).diskPair_u]
  rfl

@[simp] theorem pic_ofDiskPair
    (P : N13TwoAdicAbelChartData.DiskPair) :
    (ofDiskPair P).pic =
      N13TwoAdicAbelChartPic.DiskPair.pic P := by
  rw [(ofDiskPair P).pic_eq_diskPair_pic, diskPair_ofDiskPair]

@[simp] theorem centeredPic_ofDiskPair
    (P : N13TwoAdicAbelChartData.DiskPair) :
    (ofDiskPair P).centeredPic =
      N13TwoAdicAbelChartPic.DiskPair.centeredPic P := by
  rw [(ofDiskPair P).centeredPic_eq_diskPair_centeredPic,
    diskPair_ofDiskPair]

end NearBaseMumford

end

end MazurProof.N13TwoAdicAbelChartRecover

end
end

-- module FLT.Assumptions.MazurProof.N13AbelCompatibleGraphRecover
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13AbelCompatibleGraphRecover =====
section

/-!
# Recovering an N13 disk pair from an Abel-compatible integral graph

A special-fibre Abel equality identifies the reduced quadratic graph with
the selected divisor.  Its graph polynomial is therefore zero modulo the
reduced quadratic, but need not itself reduce coefficientwise to zero.

This file removes that harmless choice of representative.  Replacing `v`
by its monic remainder modulo `u`, and changing `w` by the resulting exact
algebraic formula, preserves the generalized Mumford equation, smoothness,
and graph ideal.  The normalized graph then satisfies the literal hypotheses
of the two-adic Hensel recovery theorem.
-/

open Polynomial

namespace MazurProof.N13AbelCompatibleGraphRecover

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13GeneralizedMumfordReduction.R₂

abbrev K : Type :=
  N13GeneralizedMumfordReduction.K

abbrev SmoothMumford₂ : Type :=
  N13GeneralizedMumfordReduction.SmoothMumford₂

/-- The quotient removed from the graph polynomial. -/
def graphQuotient (D : SmoothMumford₂) : R₂[X] :=
  D.v /ₘ D.u

/-- The canonical graph polynomial of degree strictly below `u`. -/
def normalizedV (D : SmoothMumford₂) : R₂[X] :=
  D.v %ₘ D.u

/-- The quotient in the generalized Mumford equation after replacing
`v` by its monic remainder modulo `u`. -/
def normalizedW (D : SmoothMumford₂) : R₂[X] :=
  D.w -
      graphQuotient D *
        (2 * D.v +
          N13GeneralizedMumfordIntegral.hPoly (R := R₂)) +
    D.u * graphQuotient D ^ 2

theorem normalizedV_add_mul_graphQuotient
    (D : SmoothMumford₂) :
    normalizedV D + D.u * graphQuotient D = D.v :=
  Polynomial.modByMonic_add_div D.v D.u

/-- Monic-remainder normalization preserves both the generalized curve
equation and its smoothness Bezout identity. -/
def normalizeSmoothMumford
    (D : SmoothMumford₂) : SmoothMumford₂ where
  u := D.u
  v := normalizedV D
  w := normalizedW D
  u_monic := D.u_monic
  curve_eq := by
    have hv :
        normalizedV D =
          D.v - D.u * graphQuotient D := by
      linear_combination normalizedV_add_mul_graphQuotient D
    rw [hv]
    unfold normalizedW
    calc
      (D.v - D.u * graphQuotient D) ^ 2 +
            N13GeneralizedMumfordIntegral.hPoly *
              (D.v - D.u * graphQuotient D) -
          N13GeneralizedMumfordIntegral.rhsPoly =
          (D.v ^ 2 +
                N13GeneralizedMumfordIntegral.hPoly * D.v -
              N13GeneralizedMumfordIntegral.rhsPoly) -
            D.u * graphQuotient D *
              (2 * D.v +
                N13GeneralizedMumfordIntegral.hPoly) +
            D.u ^ 2 * graphQuotient D ^ 2 := by ring
      _ =
          D.u *
            (D.w -
                graphQuotient D *
                  (2 * D.v +
                    N13GeneralizedMumfordIntegral.hPoly) +
              D.u * graphQuotient D ^ 2) := by
        rw [D.curve_eq]
        ring
  bezout := by
    obtain ⟨a, b, c, habc⟩ := D.bezout
    refine
      ⟨a + 2 * b * graphQuotient D +
          c * graphQuotient D ^ 2,
        b + c * graphQuotient D, c, ?_⟩
    have hv :
        normalizedV D =
          D.v - D.u * graphQuotient D := by
      linear_combination normalizedV_add_mul_graphQuotient D
    rw [hv]
    unfold normalizedW
    calc
      (a + 2 * b * graphQuotient D +
              c * graphQuotient D ^ 2) * D.u +
            (b + c * graphQuotient D) *
              (2 * (D.v - D.u * graphQuotient D) +
                N13GeneralizedMumfordIntegral.hPoly (R := R₂)) +
          c *
            (D.w -
                graphQuotient D *
                  (2 * D.v +
                    N13GeneralizedMumfordIntegral.hPoly (R := R₂)) +
              D.u * graphQuotient D ^ 2) =
          a * D.u +
              b *
                (2 * D.v +
                  N13GeneralizedMumfordIntegral.hPoly (R := R₂)) +
            c * D.w := by ring
      _ = 1 := habc

@[simp] theorem normalizeSmoothMumford_u
    (D : SmoothMumford₂) :
    (normalizeSmoothMumford D).u = D.u := rfl

@[simp] theorem normalizeSmoothMumford_v
    (D : SmoothMumford₂) :
    (normalizeSmoothMumford D).v = normalizedV D := rfl

/-- Normalization does not change the integral graph ideal. -/
theorem normalizeSmoothMumford_mumfordIdeal
    (D : SmoothMumford₂) :
    N13GeneralizedMumfordIntegral.mumfordIdeal
        (normalizeSmoothMumford D).u
        (normalizeSmoothMumford D).v =
      N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v := by
  exact
    N13TwoAdicAbelChartRecover.NearBaseMumford.mumfordIdeal_eq_of_dvd_sub
      D.u (normalizedV D) D.v
      (Polynomial.dvd_modByMonic_sub D.v D.u)

/-- Abel compatibility of the special fibre makes the normalized integral
graph a literal near-base graph. -/
def normalizedNearBase
    (D : SmoothMumford₂)
    (hdeg : D.u.natDegree = 2)
    (habel :
      N13AbelFiberTwoModel.abel
          (N13SpecialGraphDivisor.graphDivisor
            (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
            (N13SpecialGraphReduction.reduceSmoothMumford_u_natDegree
              D hdeg)) =
        N13AbelFiberTwoModel.abel
          N13AbelChartBase.specialBaseDivisor) :
    N13TwoAdicAbelChartRecover.NearBaseMumford where
  toSmoothMumford₂ := normalizeSmoothMumford D
  reduce_u := by
    have hgraph :=
      N13SpecialGraphDivisor.graphDivisor_eq_special_of_setAbel_eq
        (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
        (N13SpecialGraphReduction.reduceSmoothMumford_u_natDegree D hdeg)
        habel
    exact
      (N13SpecialGraphDivisor.u_eq_base_and_dvd_v_of_graphDivisor_eq
        (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
        (N13SpecialGraphReduction.reduceSmoothMumford_u_natDegree D hdeg)
        hgraph).1
  reduce_v := by
    have hgraph :=
      N13SpecialGraphDivisor.graphDivisor_eq_special_of_setAbel_eq
        (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
        (N13SpecialGraphReduction.reduceSmoothMumford_u_natDegree D hdeg)
        habel
    have hdvd :
        N13GeneralizedMumfordReduction.reducePoly D.u ∣
          N13GeneralizedMumfordReduction.reducePoly D.v :=
      (N13SpecialGraphDivisor.u_eq_base_and_dvd_v_of_graphDivisor_eq
        (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
        (N13SpecialGraphReduction.reduceSmoothMumford_u_natDegree D hdeg)
        hgraph).2
    change
      N13GeneralizedMumfordReduction.reducePoly
          (D.v %ₘ D.u) = 0
    rw [N13GeneralizedMumfordReduction.reducePoly_apply,
      Polynomial.map_modByMonic
        N13GeneralizedMumfordReduction.reduceBase D.u_monic]
    exact
      (Polynomial.modByMonic_eq_zero_iff_dvd
        (D.u_monic.map
          N13GeneralizedMumfordReduction.reduceBase)).2 hdvd

/-- The representative-level mapped-ideal equality is an equivalent and
often more convenient input than the set-valued Abel equality. -/
def normalizedNearBaseOfMappedSpecial
    (D : SmoothMumford₂)
    (hdeg : D.u.natDegree = 2)
    (hmap :
      Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
          (N13GeneralizedMumfordIntegral.mumfordIdeal
            (R := R₂) D.u D.v) =
        N13SpecialQuotientBasis.specialIdeal) :
    N13TwoAdicAbelChartRecover.NearBaseMumford :=
  normalizedNearBase D hdeg
    ((N13SpecialGraphReduction.setAbel_eq_iff_map_mumfordIdeal_eq_special
      D hdeg).2 hmap)

/-- Hensel recovery directly from the literal mapped special ideal. -/
def recoveredDiskPairOfMappedSpecial
    (D : SmoothMumford₂)
    (hdeg : D.u.natDegree = 2)
    (hmap :
      Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
          (N13GeneralizedMumfordIntegral.mumfordIdeal
            (R := R₂) D.u D.v) =
        N13SpecialQuotientBasis.specialIdeal) :
    N13TwoAdicAbelChartData.DiskPair :=
  (normalizedNearBaseOfMappedSpecial D hdeg hmap).diskPair

/-- Literal special reduction is therefore exactly enough to recover a
two-disk graph with the same integral ideal. -/
theorem mumfordIdeal_eq_recoveredDiskPairOfMappedSpecial
    (D : SmoothMumford₂)
    (hdeg : D.u.natDegree = 2)
    (hmap :
      Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
          (N13GeneralizedMumfordIntegral.mumfordIdeal
            (R := R₂) D.u D.v) =
        N13SpecialQuotientBasis.specialIdeal) :
    N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v =
      N13GeneralizedMumfordIntegral.mumfordIdeal
        (recoveredDiskPairOfMappedSpecial D hdeg hmap).u
        (recoveredDiskPairOfMappedSpecial D hdeg hmap).v := by
  unfold recoveredDiskPairOfMappedSpecial
  have hpair :=
    N13TwoAdicAbelChartRecover.NearBaseMumford.mumfordIdeal_diskPair
      (normalizedNearBaseOfMappedSpecial D hdeg hmap)
  rw [← hpair]
  exact (normalizeSmoothMumford_mumfordIdeal D).symm

end

end MazurProof.N13AbelCompatibleGraphRecover

end
end

-- module FLT.Assumptions.MazurProof.N13RankTwoQuotientAlgebra
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13RankTwoQuotientAlgebra =====
section

/-!
# Rank-two quotient algebras for the N13 integral graph

Once a relative degree-two divisor has been shown finite and flat, its
affine coordinate quotient is free of rank two with the literal basis
`{1,x}`.  This file records the structural algebra needed to recover its
Mumford equation.

A basis `{1,x}` is a power basis.  Over an arbitrary nontrivial
commutative base ring, evaluation at its generator has kernel generated by
the power-basis relation polynomial.  That polynomial is also the
characteristic polynomial of multiplication by the generator.
-/

open Module
open Polynomial

namespace MazurProof.N13RankTwoQuotientAlgebra

noncomputable section

universe u v

variable {R : Type u} {B : Type v}

section PowerBasisKernel

variable [CommRing R] [Nontrivial R]
variable [Ring B] [Algebra R B]

/-- A power basis presents its algebra as the polynomial quotient by the
relation polynomial of its generator.  The proof uses monic division and
linear independence of the power basis, so no domain hypothesis is needed. -/
theorem ker_aeval_eq_span_minpolyGen
    (pb : PowerBasis R B) :
    RingHom.ker (aeval pb.gen) =
      Ideal.span ({pb.minpolyGen} : Set R[X]) := by
  apply le_antisymm
  · intro p hp
    rw [Ideal.mem_span_singleton]
    have hpRoot : aeval pb.gen p = 0 :=
      RingHom.mem_ker.mp hp
    have hremRoot :
        aeval pb.gen (p %ₘ pb.minpolyGen) = 0 := by
      have hdiv :=
        modByMonic_add_div p pb.minpolyGen
      calc
        aeval pb.gen (p %ₘ pb.minpolyGen) =
            aeval pb.gen
              (p - pb.minpolyGen * (p /ₘ pb.minpolyGen)) := by
          congr 1
          exact eq_sub_of_add_eq hdiv
        _ =
            aeval pb.gen p -
              aeval pb.gen pb.minpolyGen *
                aeval pb.gen (p /ₘ pb.minpolyGen) := by
          simp only [map_sub, map_mul]
        _ = 0 := by
          rw [hpRoot, pb.aeval_minpolyGen, zero_mul, sub_zero]
    have hrem :
        p %ₘ pb.minpolyGen = 0 := by
      by_contra hne
      have hle :=
        pb.dim_le_degree_of_root hne hremRoot
      have hlt :
          degree (p %ₘ pb.minpolyGen) < pb.dim := by
        simpa [pb.degree_minpolyGen] using
          degree_modByMonic_lt p pb.minpolyGen_monic
      exact (not_le_of_gt hlt) hle
    exact
      (modByMonic_eq_zero_iff_dvd pb.minpolyGen_monic).mp hrem
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact RingHom.mem_ker.mpr pb.aeval_minpolyGen

end PowerBasisKernel

section CharacteristicPolynomial

variable [CommRing R]
variable [Ring B] [Algebra R B]
variable [Module.Free R B] [Module.Finite R B]

/-- The characteristic polynomial of multiplication by the generator is
the power-basis relation polynomial. -/
theorem charpoly_lmul_eq_minpolyGen
    (pb : PowerBasis R B) :
    (Algebra.lmul R B pb.gen).charpoly =
      pb.minpolyGen := by
  rw [← LinearMap.charpoly_toMatrix
      (Algebra.lmul R B pb.gen) pb.basis,
    ← Algebra.leftMulMatrix_apply,
    charpoly_leftMulMatrix,
    ← pb.minpolyGen_eq]

/-- Hence the evaluation kernel is generated by the characteristic
polynomial of multiplication by the power-basis generator. -/
theorem ker_aeval_eq_span_charpoly
    [Nontrivial R]
    (pb : PowerBasis R B) :
    RingHom.ker (aeval pb.gen) =
      Ideal.span
        ({(Algebra.lmul R B pb.gen).charpoly} : Set R[X]) := by
  rw [charpoly_lmul_eq_minpolyGen]
  exact ker_aeval_eq_span_minpolyGen pb

end CharacteristicPolynomial

section LiteralOneXBasis

variable [CommRing R]
variable [Ring B] [Algebra R B]

/-- A literal rank-two basis `{1,x}` is a power basis generated by `x`. -/
def powerBasisOfOneX
    (x : B) (b : Basis (Fin 2) R B)
    (hb0 : b 0 = 1) (hb1 : b 1 = x) :
    PowerBasis R B where
  gen := x
  dim := 2
  basis := b
  basis_eq_pow i := by
    fin_cases i
    · simpa using hb0
    · simpa using hb1

@[simp] theorem powerBasisOfOneX_gen
    (x : B) (b : Basis (Fin 2) R B)
    (hb0 : b 0 = 1) (hb1 : b 1 = x) :
    (powerBasisOfOneX x b hb0 hb1).gen = x := rfl

@[simp] theorem powerBasisOfOneX_dim
    (x : B) (b : Basis (Fin 2) R B)
    (hb0 : b 0 = 1) (hb1 : b 1 = x) :
    (powerBasisOfOneX x b hb0 hb1).dim = 2 := rfl

/-- Kernel presentation specialized to a literal rank-two basis `{1,x}`. -/
theorem ker_aeval_eq_span_charpoly_of_one_x
    [Nontrivial R]
    [Module.Free R B] [Module.Finite R B]
    (x : B) (b : Basis (Fin 2) R B)
    (hb0 : b 0 = 1) (hb1 : b 1 = x) :
    RingHom.ker (aeval x) =
      Ideal.span
        ({(Algebra.lmul R B x).charpoly} : Set R[X]) := by
  simpa using
    ker_aeval_eq_span_charpoly
      (powerBasisOfOneX x b hb0 hb1)

/-- The multiplication characteristic polynomial is monic. -/
theorem charpoly_lmul_monic_of_one_x
    [Module.Free R B] [Module.Finite R B]
    (x : B) :
    (Algebra.lmul R B x).charpoly.Monic :=
  LinearMap.charpoly_monic _

/-- For a rank-two power basis, the multiplication characteristic
polynomial has degree exactly two. -/
theorem charpoly_lmul_natDegree_of_one_x
    [Nontrivial R]
    [Module.Free R B] [Module.Finite R B]
    (x : B) (b : Basis (Fin 2) R B)
    (hb0 : b 0 = 1) (hb1 : b 1 = x) :
    (Algebra.lmul R B x).charpoly.natDegree = 2 := by
  let pb := powerBasisOfOneX x b hb0 hb1
  calc
    (Algebra.lmul R B x).charpoly.natDegree =
        pb.minpolyGen.natDegree := by
      rw [show x = pb.gen by rfl,
        charpoly_lmul_eq_minpolyGen]
    _ = pb.dim := pb.natDegree_minpolyGen
    _ = 2 := rfl

/-- Every element of a rank-two algebra with basis `{1,x}` has a unique
linear-polynomial expression in `x`; only existence is needed downstream. -/
theorem exists_eq_algebraMap_add_algebraMap_mul
    [Nontrivial R] [Nontrivial B]
    (x y : B) (b : Basis (Fin 2) R B)
    (hb0 : b 0 = 1) (hb1 : b 1 = x) :
    ∃ a c : R,
      y = algebraMap R B a + algebraMap R B c * x := by
  let pb := powerBasisOfOneX x b hb0 hb1
  obtain ⟨f, hf, hy⟩ := pb.exists_eq_aeval y
  have hf' : f.natDegree ≤ 1 := by
    simpa [pb] using Nat.le_of_lt_succ hf
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hf'] at hy
  have hy' :
      y =
        algebraMap R B (f.coeff 1) * x +
          algebraMap R B (f.coeff 0) := by
    simpa [pb] using hy
  calc
    y =
        algebraMap R B (f.coeff 1) * x +
          algebraMap R B (f.coeff 0) := hy'
    _ =
        algebraMap R B (f.coeff 0) +
          algebraMap R B (f.coeff 1) * x := by
      rw [add_comm]

end LiteralOneXBasis

end

end MazurProof.N13RankTwoQuotientAlgebra

end
end

-- module FLT.Assumptions.MazurProof.N13RankTwoIdealRecovery
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13RankTwoIdealRecovery =====
section

/-!
# Recovering the literal graph ideal from a rank-two quotient

Once a quotient has basis `{1,x̄}`, the characteristic polynomial `u` of
multiplication by `x̄` generates the evaluation kernel.  Expressing `ȳ` as
`v(x̄)` then recovers the original ambient ideal literally as

`(u(x), y-v(x))`.

This is an ideal-correspondence argument.  It does not assume that the
original ideal was already given in Mumford graph form.
-/

open Polynomial

namespace MazurProof.N13RankTwoIdealRecovery

noncomputable section

universe uR uA

variable {R : Type uR} {A : Type uA}
variable [CommRing R] [CommRing A] [Algebra R A]

/-- Polynomial normal form of degree at most one in the second coordinate. -/
def HasRankTwoPolynomialNormalForm (x y : A) : Prop :=
  ∀ a : A, ∃ p q : R[X],
    a = aeval x p + aeval x q * y

/--
If evaluation at `x̄` has kernel `(u)` and `ȳ=v(x̄)`, then the ambient
ideal is exactly `(u(x),y-v(x))`.
-/
theorem ideal_eq_span_aeval_y_sub
    (x y : A)
    (I : Ideal A)
    (u v : R[X])
    (hnormal : HasRankTwoPolynomialNormalForm (R := R) x y)
    (hker :
      RingHom.ker
          ((aeval (Ideal.Quotient.mk I x) :
              R[X] →ₐ[R] A ⧸ I).toRingHom) =
        Ideal.span ({u} : Set R[X]))
    (hy :
      Ideal.Quotient.mk I y =
        aeval (Ideal.Quotient.mk I x) v) :
    I =
      Ideal.span
        ({aeval x u, y - aeval x v} : Set A) := by
  let π : A →ₐ[R] A ⧸ I := Ideal.Quotient.mkₐ R I
  have hker' :
      RingHom.ker
          ((aeval (π x) : R[X] →ₐ[R] A ⧸ I).toRingHom) =
        Ideal.span ({u} : Set R[X]) := by
    simpa [π] using hker
  have hy' : π y = aeval (π x) v := by
    simpa [π] using hy
  apply le_antisymm
  · intro a ha
    obtain ⟨p, q, hform⟩ := hnormal a
    have ha0 : π a = 0 := by
      simpa [π] using
        (Ideal.Quotient.eq_zero_iff_mem.mpr ha)
    have hpoly0 :
        aeval (π x) (p + q * v) = 0 := by
      calc
        aeval (π x) (p + q * v) =
            aeval (π x) p +
              aeval (π x) q * aeval (π x) v := by
          simp only [map_add, map_mul]
        _ =
            aeval (π x) p +
              aeval (π x) q * π y := by
          rw [← hy']
        _ =
            π (aeval x p) +
              π (aeval x q) * π y := by
          rw [Polynomial.aeval_algHom_apply π x p,
            Polynomial.aeval_algHom_apply π x q]
        _ = π (aeval x p + aeval x q * y) := by
          rw [map_add, map_mul]
        _ = π a := by rw [← hform]
        _ = 0 := ha0
    have hpqSpan :
        p + q * v ∈ Ideal.span ({u} : Set R[X]) := by
      rw [← hker']
      exact RingHom.mem_ker.mpr hpoly0
    obtain ⟨w, hw⟩ :=
      Ideal.mem_span_singleton.mp hpqSpan
    refine
      (Ideal.mem_span_pair).2
        ⟨aeval x w, aeval x q, ?_⟩
    calc
      aeval x w * aeval x u +
          aeval x q * (y - aeval x v) =
        aeval x (u * w) +
          aeval x q * y -
          aeval x (q * v) := by
        simp only [map_mul]
        ring
      _ =
        aeval x (p + q * v) +
          aeval x q * y -
          aeval x (q * v) := by
        rw [← hw]
      _ = aeval x p + aeval x q * y := by
        simp only [map_add, map_mul]
        ring
      _ = a := hform.symm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · have huKer :
          u ∈
            RingHom.ker
              ((aeval (π x) :
                  R[X] →ₐ[R] A ⧸ I).toRingHom) := by
        rw [hker']
        exact Ideal.mem_span_singleton_self u
      have hzero : π (aeval x u) = 0 := by
        calc
          π (aeval x u) = aeval (π x) u :=
            (Polynomial.aeval_algHom_apply π x u).symm
          _ = 0 := RingHom.mem_ker.mp huKer
      exact
        Ideal.Quotient.eq_zero_iff_mem.mp
          (by simpa [π] using hzero)
    · have hzero : π (y - aeval x v) = 0 := by
        calc
          π (y - aeval x v) =
              π y - π (aeval x v) := by
            exact map_sub π y (aeval x v)
          _ = π y - aeval (π x) v := by
            rw [← Polynomial.aeval_algHom_apply π x v]
          _ = 0 := by rw [hy', sub_self]
      exact
        Ideal.Quotient.eq_zero_iff_mem.mp
          (by simpa [π] using hzero)

end

end MazurProof.N13RankTwoIdealRecovery

end
end

-- module FLT.Assumptions.MazurProof.N13QuotientReduction
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13QuotientReduction =====
section

/-!
# Reduction of N13 affine quotients

A surjective ambient reduction map descends along a literal mapped-ideal
equality.  The kernel of the descended map is exactly the image of the
ambient kernel.  For the N13 integral model this is the principal ideal
generated by the quotient class of `2`.

No flatness, saturation, or chosen Mumford presentation is used here.
-/

namespace MazurProof.N13QuotientReduction

noncomputable section

universe uA uS

variable {A : Type uA} {S : Type uS}
variable [CommRing A] [CommRing S]

theorem sourceIdeal_le_ker_quotientComp
    (f : A →+* S)
    (I : Ideal A)
    (J : Ideal S)
    (hmap : Ideal.map f I = J) :
    I ≤ RingHom.ker ((Ideal.Quotient.mk J).comp f) := by
  intro a ha
  rw [RingHom.mem_ker, RingHom.comp_apply,
    Ideal.Quotient.eq_zero_iff_mem, ← hmap]
  exact Ideal.mem_map_of_mem f ha

/-- The quotient map induced by a ring map carrying the source ideal
literally onto the target ideal. -/
def inducedQuotientMap
    (f : A →+* S)
    (I : Ideal A)
    (J : Ideal S)
    (hmap : Ideal.map f I = J) :
    A ⧸ I →+* S ⧸ J :=
  Ideal.Quotient.lift I
    ((Ideal.Quotient.mk J).comp f)
    (sourceIdeal_le_ker_quotientComp f I J hmap)

@[simp] theorem inducedQuotientMap_mk
    (f : A →+* S)
    (I : Ideal A)
    (J : Ideal S)
    (hmap : Ideal.map f I = J)
    (a : A) :
    inducedQuotientMap f I J hmap
        (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk J (f a) :=
  rfl

/-- Surjectivity descends to the quotient rings. -/
theorem inducedQuotientMap_surjective
    (f : A →+* S)
    (hf : Function.Surjective f)
    (I : Ideal A)
    (J : Ideal S)
    (hmap : Ideal.map f I = J) :
    Function.Surjective
      (inducedQuotientMap f I J hmap) := by
  unfold inducedQuotientMap
  apply Ideal.Quotient.lift_surjective_of_surjective
  exact Ideal.Quotient.mk_surjective.comp hf

/-- For a surjective ambient map, the quotient kernel is the image of the
ambient kernel. -/
theorem ker_inducedQuotientMap_eq_map_ker
    (f : A →+* S)
    (hf : Function.Surjective f)
    (I : Ideal A)
    (J : Ideal S)
    (hmap : Ideal.map f I = J) :
    RingHom.ker (inducedQuotientMap f I J hmap) =
      Ideal.map (Ideal.Quotient.mk I) (RingHom.ker f) := by
  have hkerComp :
      RingHom.ker ((Ideal.Quotient.mk J).comp f) =
        I ⊔ RingHom.ker f := by
    calc
      RingHom.ker ((Ideal.Quotient.mk J).comp f) =
          Ideal.comap f
            (RingHom.ker (Ideal.Quotient.mk J)) :=
        (RingHom.comap_ker (Ideal.Quotient.mk J) f).symm
      _ = Ideal.comap f J := by
        rw [Ideal.mk_ker]
      _ = Ideal.comap f (Ideal.map f I) :=
        congrArg (Ideal.comap f) hmap.symm
      _ = I ⊔ Ideal.comap f (⊥ : Ideal S) :=
        Ideal.comap_map_of_surjective f hf I
      _ = I ⊔ RingHom.ker f := by
        rfl
  unfold inducedQuotientMap
  rw [Ideal.ker_quotient_lift, hkerComp,
    Ideal.map_sup, Ideal.map_quotient_self]
  simp

/-- A principal ambient kernel remains principal after quotienting. -/
theorem ker_inducedQuotientMap_eq_span
    (f : A →+* S)
    (hf : Function.Surjective f)
    (I : Ideal A)
    (J : Ideal S)
    (hmap : Ideal.map f I = J)
    (r : A)
    (hker :
      RingHom.ker f = Ideal.span ({r} : Set A)) :
    RingHom.ker (inducedQuotientMap f I J hmap) =
      Ideal.span
        ({Ideal.Quotient.mk I r} : Set (A ⧸ I)) := by
  rw [ker_inducedQuotientMap_eq_map_ker
      f hf I J hmap,
    hker, Ideal.map_span]
  simp

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13GeneralizedMumfordReduction.R₂

abbrev IntegralRing : Type :=
  N13GeneralizedMumfordReduction.IntegralRing

abbrev SpecialRing : Type :=
  N13GeneralizedMumfordReduction.SpecialRing

/-- N13 coefficient reduction descended along a mapped-ideal equality. -/
def reduceCoordinateQuotient
    (I : Ideal IntegralRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        J) :
    IntegralRing ⧸ I →+* SpecialRing ⧸ J :=
  inducedQuotientMap
    N13GeneralizedMumfordReduction.reduceCoordinate I J hmap

@[simp] theorem reduceCoordinateQuotient_mk
    (I : Ideal IntegralRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        J)
    (a : IntegralRing) :
    reduceCoordinateQuotient I J hmap
        (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk J
        (N13GeneralizedMumfordReduction.reduceCoordinate a) :=
  rfl

theorem reduceCoordinateQuotient_surjective
    (I : Ideal IntegralRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        J) :
    Function.Surjective
      (reduceCoordinateQuotient I J hmap) := by
  exact
    inducedQuotientMap_surjective
      N13GeneralizedMumfordReduction.reduceCoordinate
      N13GeneralizedMumfordReduction.reduceCoordinate_surjective
      I J hmap

/-- The descended N13 reduction kernel is generated by the quotient class
of the vertical parameter `2`. -/
theorem ker_reduceCoordinateQuotient
    (I : Ideal IntegralRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        J) :
    RingHom.ker (reduceCoordinateQuotient I J hmap) =
      Ideal.span
        ({Ideal.Quotient.mk I
            (algebraMap R₂ IntegralRing (2 : R₂))} :
          Set (IntegralRing ⧸ I)) := by
  exact
    ker_inducedQuotientMap_eq_span
      N13GeneralizedMumfordReduction.reduceCoordinate
      N13GeneralizedMumfordReduction.reduceCoordinate_surjective
      I J hmap
      (algebraMap R₂ IntegralRing (2 : R₂))
      N13GeneralizedMumfordReduction.ker_reduceCoordinate

/-- Equivalent scalar-algebra-map spelling of the same kernel. -/
theorem ker_reduceCoordinateQuotient_eq_span_two
    (I : Ideal IntegralRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        J) :
    RingHom.ker (reduceCoordinateQuotient I J hmap) =
      Ideal.span
        ({algebraMap R₂ (IntegralRing ⧸ I) (2 : R₂)} :
          Set (IntegralRing ⧸ I)) := by
  simpa only [Ideal.Quotient.mk_algebraMap] using
    ker_reduceCoordinateQuotient I J hmap

end

end MazurProof.N13QuotientReduction

end
end

-- module FLT.Assumptions.MazurProof.SexticMumfordQuotientBasis
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordQuotientBasis =====
section

/-!
# The literal basis of a quadratic sextic Mumford quotient

For a monic degree-two Mumford polynomial `u`, graph evaluation identifies
the affine quotient by `(u,Y-v)` with `K[X]/(u)`.  Transporting the canonical
power basis gives the literal quotient basis `{1,x}`.
-/

open Module
open Polynomial

namespace MazurProof.SexticMumfordQuotientBasis

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (M : SexticMumford.Model K)
variable (D : SexticMumford.SemiMumford M)

/-- The monic polynomial quotient has its canonical quadratic power basis. -/
def residueBasis
    (hdeg : D.u.natDegree = 2) :
    Basis (Fin 2) K (AdjoinRoot D.u) :=
  (AdjoinRoot.powerBasis' D.u_monic).basis.reindex
    (finCongr hdeg)

theorem residueBasis_apply
    (hdeg : D.u.natDegree = 2) (i : Fin 2) :
    residueBasis M D hdeg i =
      AdjoinRoot.root D.u ^ (i : ℕ) := by
  change
    ((AdjoinRoot.powerBasis' D.u_monic).basis.reindex
        (finCongr hdeg)) i =
      AdjoinRoot.root D.u ^ (i : ℕ)
  rw [Basis.reindex_apply, PowerBasis.basis_eq_pow,
    finCongr_symm_apply, Fin.val_cast,
    AdjoinRoot.powerBasis'_gen]

@[simp] theorem residueBasis_zero
    (hdeg : D.u.natDegree = 2) :
    residueBasis M D hdeg (0 : Fin 2) = 1 := by
  simp [residueBasis_apply]

@[simp] theorem residueBasis_one
    (hdeg : D.u.natDegree = 2) :
    residueBasis M D hdeg (1 : Fin 2) =
      AdjoinRoot.root D.u := by
  simp [residueBasis_apply]

/-- Transport the polynomial quotient basis to the affine graph quotient. -/
def quotientBasis
    (hdeg : D.u.natDegree = 2) :
    Basis (Fin 2) K
      (SexticMumford.CoordinateRing M ⧸
        SexticMumford.mumfordIdeal M D.u D.v) :=
  (residueBasis M D hdeg).map
    (SexticMumford.mumfordQuotientAlgEquiv M D).symm.toLinearEquiv

@[simp] theorem quotientBasis_zero
    (hdeg : D.u.natDegree = 2) :
    quotientBasis M D hdeg (0 : Fin 2) = 1 := by
  change
    (SexticMumford.mumfordQuotientAlgEquiv M D).symm
        (residueBasis M D hdeg 0) = 1
  rw [residueBasis_zero]
  exact map_one (SexticMumford.mumfordQuotientAlgEquiv M D).symm

@[simp] theorem quotientBasis_one
    (hdeg : D.u.natDegree = 2) :
    quotientBasis M D hdeg (1 : Fin 2) =
      Ideal.Quotient.mk
        (SexticMumford.mumfordIdeal M D.u D.v)
        (SexticMumford.xClass M X) := by
  change
    (SexticMumford.mumfordQuotientAlgEquiv M D).symm
        (residueBasis M D hdeg 1) =
      Ideal.Quotient.mk
        (SexticMumford.mumfordIdeal M D.u D.v)
        (SexticMumford.xClass M X)
  rw [residueBasis_one]
  apply (SexticMumford.mumfordQuotientAlgEquiv M D).injective
  rw [(SexticMumford.mumfordQuotientAlgEquiv M D).apply_symm_apply]
  simp only [SexticMumford.mumfordQuotientAlgEquiv]
  change
    AdjoinRoot.root D.u =
      SexticMumford.mumfordEval M D
        (SexticMumford.xClass M X)
  rw [SexticMumford.mumfordEval_xClass]
  rfl

end

end MazurProof.SexticMumfordQuotientBasis

end
end

-- module FLT.Assumptions.MazurProof.N13CanonicalContractionQuotient
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13CanonicalContractionQuotient =====
section

/-!
# Generic quotient of a canonical N13 contraction

Extending a canonical vertical contraction to the generic fibre recovers the
original ideal.  The induced map on affine quotients is injective: membership
in the contraction is definitionally membership of the image in the generic
ideal.  For a quadratic Mumford graph, this map carries the literal integral
classes of `1` and `x` to the literal generic quotient basis `{1,x}`.
-/

open Polynomial

namespace MazurProof.N13CanonicalContractionQuotient

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralModelContraction.R₂

abbrev Q₂ : Type :=
  N13IntegralModelContraction.Q₂

abbrev IntegralRing : Type :=
  N13IntegralModelContraction.IntegralRing

abbrev RationalRing : Type :=
  N13IntegralModelContraction.RationalRing

abbrev Model : SexticMumford.Model Q₂ :=
  N13GoodSexticCoordinateEquiv.M (K := Q₂)

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra

/-- The quotient map from a canonical contraction to its generic ideal. -/
def genericQuotientMap (J : Ideal RationalRing) :
    IntegralRing ⧸ N13IntegralModelContraction.contractIdeal J →+*
      RationalRing ⧸ J :=
  N13QuotientReduction.inducedQuotientMap
    N13TwoAdicCoordinateBaseChange.integralToSextic
    (N13IntegralModelContraction.contractIdeal J)
    J
    (N13IntegralModelContraction.map_contractIdeal J)

@[simp] theorem genericQuotientMap_mk
    (J : Ideal RationalRing) (a : IntegralRing) :
    genericQuotientMap J
        (Ideal.Quotient.mk
          (N13IntegralModelContraction.contractIdeal J) a) =
      Ideal.Quotient.mk J
        (N13TwoAdicCoordinateBaseChange.integralToSextic a) :=
  rfl

/-- No element is lost when passing from the contracted quotient to the
generic quotient. -/
theorem genericQuotientMap_injective
    (J : Ideal RationalRing) :
    Function.Injective (genericQuotientMap J) := by
  intro z w hzw
  apply sub_eq_zero.mp
  obtain ⟨a, ha⟩ :=
    Ideal.Quotient.mk_surjective (z - w)
  rw [← ha]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change
    N13TwoAdicCoordinateBaseChange.integralToSextic a ∈ J
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  calc
    Ideal.Quotient.mk J
        (N13TwoAdicCoordinateBaseChange.integralToSextic a) =
        genericQuotientMap J
          (Ideal.Quotient.mk
            (N13IntegralModelContraction.contractIdeal J) a) := rfl
    _ = genericQuotientMap J (z - w) :=
      congrArg (genericQuotientMap J) ha
    _ = genericQuotientMap J z -
        genericQuotientMap J w := map_sub _ z w
    _ = 0 := by rw [hzw, sub_self]

/-- The generic quotient map respects the two-adic coefficient action. -/
theorem genericQuotientMap_comp_algebraMap
    (J : Ideal RationalRing) :
    (genericQuotientMap J).comp
        (algebraMap R₂
          (IntegralRing ⧸
            N13IntegralModelContraction.contractIdeal J)) =
      algebraMap R₂ (RationalRing ⧸ J) := by
  ext r
  change
    Ideal.Quotient.mk J
        (N13TwoAdicCoordinateBaseChange.integralToSextic
          (algebraMap R₂ IntegralRing r)) =
      Ideal.Quotient.mk J (algebraMap R₂ RationalRing r)
  congr 1
  change
    N13GoodSexticCoordinateEquiv.toSextic
        (N13IntegralModelContraction.integralToGood
          (algebraMap R₂ IntegralRing r)) =
      algebraMap R₂ RationalRing r
  rw [N13IntegralModelContraction.integralToGood_algebraMap,
    N13GoodSexticCoordinateEquiv.toSextic_algebraMap]
  exact
    (IsScalarTower.algebraMap_apply R₂ Q₂ RationalRing r).symm

/-- The integral affine `x` coordinate. -/
def integralX : IntegralRing :=
  N13GeneralizedMumfordIntegral.xClass (R := R₂) X

@[simp] theorem integralToSextic_integralX :
    N13TwoAdicCoordinateBaseChange.integralToSextic integralX =
      SexticMumford.xClass Model X := by
  simp [integralX,
    N13TwoAdicCoordinateBaseChange.integralToSextic]

/-- The generic graph ideal of sextic Mumford data. -/
abbrev graphIdeal
    (D : SexticMumford.SemiMumford Model) :
    Ideal RationalRing :=
  SexticMumford.mumfordIdeal Model D.u D.v

/-- The canonical contraction map sends `1` to the zero-th literal generic
basis vector. -/
theorem genericQuotientMap_one_eq_basis_zero
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2) :
    genericQuotientMap (graphIdeal D)
        (1 :
          IntegralRing ⧸
            N13IntegralModelContraction.contractIdeal
              (graphIdeal D)) =
      SexticMumfordQuotientBasis.quotientBasis
        Model D hdeg 0 := by
  simp

/-- The canonical contraction map sends the integral class of `x` to the
first literal generic basis vector. -/
theorem genericQuotientMap_x_eq_basis_one
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2) :
    genericQuotientMap (graphIdeal D)
        (Ideal.Quotient.mk
          (N13IntegralModelContraction.contractIdeal
            (graphIdeal D))
          integralX) =
      SexticMumfordQuotientBasis.quotientBasis
        Model D hdeg 1 := by
  rw [genericQuotientMap_mk,
    integralToSextic_integralX,
    SexticMumfordQuotientBasis.quotientBasis_one]

end

end MazurProof.N13CanonicalContractionQuotient

end
end

-- module FLT.Assumptions.MazurProof.N13QuotientVerticalFlatness
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13QuotientVerticalFlatness =====
section

/-!
# Vertical saturation gives flat N13 quotients

The canonical contraction of a generic ideal is saturated with respect to
every nonzero two-adic scalar.  Consequently its affine quotient has no
two-adic torsion.  Since the two-adic integers form a Dedekind domain, the
quotient is flat even before finiteness has been established.

This separates the easy vertical part of the two-fibre argument from the
genuine no-escape/finiteness step.
-/

namespace MazurProof.N13QuotientVerticalFlatness

noncomputable section

universe uR uA

variable {R : Type uR} {A : Type uA}
variable [CommRing R] [IsDomain R]
variable [CommRing A] [Algebra R A]

/--
An ideal saturated with respect to every nonzero base scalar has a
torsion-free quotient over the base.
-/
theorem quotient_isTorsionFree_of_scalar_saturated
    (I : Ideal A)
    (hsaturated :
      ∀ (r : R), r ≠ 0 →
        ∀ a : A, algebraMap R A r * a ∈ I → a ∈ I) :
    Module.IsTorsionFree R (A ⧸ I) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r z hrz
  by_cases hr : r = 0
  · exact Or.inl hr
  · right
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply hsaturated r hr a
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul]
    change
      algebraMap R (A ⧸ I) r *
          Ideal.Quotient.mk I a = 0
    simpa only [Algebra.smul_def] using hrz

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralModelContraction.R₂

abbrev IntegralRing : Type :=
  N13IntegralModelContraction.IntegralRing

abbrev RationalRing : Type :=
  N13IntegralModelContraction.RationalRing

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra

/-- The quotient by a canonical vertical contraction is two-adically
torsion-free. -/
theorem contractQuotient_isTorsionFree
    (J : Ideal RationalRing) :
    Module.IsTorsionFree R₂
      (IntegralRing ⧸
        N13IntegralModelContraction.contractIdeal J) := by
  apply quotient_isTorsionFree_of_scalar_saturated
  intro r hr a ha
  exact
    N13IntegralModelContraction.contractIdeal_vertical_saturated
      J r hr ha

/-- Over the two-adic DVR the same quotient is flat, with no finiteness
assumption. -/
theorem contractQuotient_flat
    (J : Ideal RationalRing) :
    Module.Flat R₂
      (IntegralRing ⧸
        N13IntegralModelContraction.contractIdeal J) := by
  letI :
      Module.IsTorsionFree R₂
        (IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal J) :=
    contractQuotient_isTorsionFree J
  infer_instance

end

end MazurProof.N13QuotientVerticalFlatness

end
end

-- module FLT.Assumptions.MazurProof.N13TensorSpecialFiber
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TensorSpecialFiber =====
section

/-!
# Identifying a tensor special fibre from its quotient map

Suppose a surjective quotient-reduction map has kernel generated by the
image of a uniformizer.  Tensoring with the residue field then gives the
target quotient exactly.  The proof uses pure tensors and moves the
uniformizer to the residue-field factor; it does not identify a separate
quotient of the source ideal.
-/

open scoped TensorProduct
open Module

namespace MazurProof.N13TensorSpecialFiber

noncomputable section

universe uR uk uB uC uι

variable {R : Type uR} {k : Type uk}
variable {B : Type uB} {C : Type uC}
variable [CommRing R] [CommRing k]
variable [CommRing B] [CommRing C]
variable [Algebra R k] [Algebra R B] [Algebra R C]
variable [Algebra k C] [IsScalarTower R k C]

/-- Regard a ring homomorphism as an `R`-algebra homomorphism through the
supplied scalar factorization. -/
def factoredAlgHom
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k)) :
    B →ₐ[R] C where
  toRingHom := g
  commutes' r := by
    calc
      g (algebraMap R B r) =
          algebraMap k C (algebraMap R k r) := by
        simpa only [RingHom.comp_apply] using
          DFunLike.congr_fun hfactor r
      _ = algebraMap R C r :=
        (IsScalarTower.algebraMap_apply R k C r).symm

@[simp] theorem factoredAlgHom_apply
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k))
    (b : B) :
    factoredAlgHom g hfactor b = g b :=
  rfl

/-- The canonical map `a ⊗ b ↦ a • g(b)`. -/
def tensorLinearMap
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k)) :
    k ⊗[R] B →ₗ[k] C :=
  (factoredAlgHom g hfactor).toLinearMap.liftBaseChange k

@[simp] theorem tensorLinearMap_tmul
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k))
    (a : k) (b : B) :
    tensorLinearMap g hfactor (a ⊗ₜ[R] b) =
      a • g b := by
  simp [tensorLinearMap]

theorem tensorLinearMap_eq_zero
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k))
    (hq : Function.Surjective (algebraMap R k))
    (π : R)
    (hπ : algebraMap R k π = 0)
    (hker :
      RingHom.ker g =
        Ideal.span ({algebraMap R B π} : Set B))
    {z : k ⊗[R] B}
    (hz : tensorLinearMap g hfactor z = 0) :
    z = 0 := by
  obtain ⟨b, rfl⟩ :=
    (TensorProduct.mk_surjective R B k hq) z
  change
    tensorLinearMap g hfactor
        ((1 : k) ⊗ₜ[R] b) = 0 at hz
  change (1 : k) ⊗ₜ[R] b = 0
  have hgb : g b = 0 := by
    simpa only [tensorLinearMap_tmul, one_smul] using hz
  have hbker : b ∈ RingHom.ker g :=
    RingHom.mem_ker.mpr hgb
  rw [hker, Ideal.mem_span_singleton] at hbker
  obtain ⟨c, rfl⟩ := hbker
  calc
    (1 : k) ⊗ₜ[R] (algebraMap R B π * c) =
        (1 : k) ⊗ₜ[R] (π • c) := by
      rw [Algebra.smul_def]
    _ = (π • (1 : k)) ⊗ₜ[R] c :=
      (TensorProduct.smul_tmul
        (R := R) π (1 : k) c).symm
    _ = 0 := by
      simp only [Algebra.smul_def, hπ, zero_mul,
        TensorProduct.zero_tmul]

theorem tensorLinearMap_injective
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k))
    (hq : Function.Surjective (algebraMap R k))
    (π : R)
    (hπ : algebraMap R k π = 0)
    (hker :
      RingHom.ker g =
        Ideal.span ({algebraMap R B π} : Set B)) :
    Function.Injective (tensorLinearMap g hfactor) := by
  intro z₁ z₂ hz
  have hzero :
      tensorLinearMap g hfactor (z₁ - z₂) = 0 := by
    simpa only [map_sub, hz, sub_self]
  exact sub_eq_zero.mp
    (tensorLinearMap_eq_zero
      (g := g) (hfactor := hfactor)
      (hq := hq) (π := π) (hπ := hπ)
      (hker := hker) hzero)

theorem tensorLinearMap_surjective
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k))
    (hg : Function.Surjective g) :
    Function.Surjective (tensorLinearMap g hfactor) := by
  intro c
  obtain ⟨b, rfl⟩ := hg c
  exact ⟨(1 : k) ⊗ₜ[R] b, by simp⟩

/-- The explicit linear equivalence between the tensor special fibre and
the target quotient. -/
def tensorLinearEquiv
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k))
    (hq : Function.Surjective (algebraMap R k))
    (π : R)
    (hπ : algebraMap R k π = 0)
    (hg : Function.Surjective g)
    (hker :
      RingHom.ker g =
        Ideal.span ({algebraMap R B π} : Set B)) :
    k ⊗[R] B ≃ₗ[k] C :=
  LinearEquiv.ofBijective (tensorLinearMap g hfactor)
    ⟨tensorLinearMap_injective
        (g := g) (hfactor := hfactor)
        (hq := hq) (π := π) (hπ := hπ)
        (hker := hker),
      tensorLinearMap_surjective
        (g := g) (hfactor := hfactor) hg⟩

@[simp] theorem tensorLinearEquiv_tmul
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k))
    (hq : Function.Surjective (algebraMap R k))
    (π : R)
    (hπ : algebraMap R k π = 0)
    (hg : Function.Surjective g)
    (hker :
      RingHom.ker g =
        Ideal.span ({algebraMap R B π} : Set B))
    (a : k) (b : B) :
    tensorLinearEquiv g hfactor hq π hπ hg hker
        (a ⊗ₜ[R] b) =
      a • g b := by
  exact tensorLinearMap_tmul g hfactor a b

section ResidueField

variable [IsLocalRing R]


variable [Algebra (IsLocalRing.ResidueField R) C]
variable [IsScalarTower R (IsLocalRing.ResidueField R) C]

theorem residueFactor
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap (IsLocalRing.ResidueField R) C).comp (IsLocalRing.residue R)) :
    g.comp (algebraMap R B) =
      (algebraMap (IsLocalRing.ResidueField R) C).comp (algebraMap R (IsLocalRing.ResidueField R)) := by
  simpa only [IsLocalRing.ResidueField.algebraMap_eq R] using hfactor

theorem residueAlgebraMap_surjective :
    Function.Surjective (algebraMap R (IsLocalRing.ResidueField R)) := by
  simpa only [IsLocalRing.ResidueField.algebraMap_eq R] using
    (IsLocalRing.residue_surjective (R := R))

theorem residueElement_eq_zero
    (π : R)
    (hπ : π ∈ IsLocalRing.maximalIdeal R) :
    algebraMap R (IsLocalRing.ResidueField R) π = 0 := by
  rw [IsLocalRing.ResidueField.algebraMap_eq R,
    IsLocalRing.residue_eq_zero_iff]
  exact hπ

/-- Residue-field specialization of `tensorLinearEquiv`. -/
def residueLinearEquiv
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap (IsLocalRing.ResidueField R) C).comp (IsLocalRing.residue R))
    (π : R)
    (hπ : π ∈ IsLocalRing.maximalIdeal R)
    (hg : Function.Surjective g)
    (hker :
      RingHom.ker g =
        Ideal.span ({algebraMap R B π} : Set B)) :
    (IsLocalRing.ResidueField R) ⊗[R] B ≃ₗ[(IsLocalRing.ResidueField R)] C :=
  tensorLinearEquiv
    (g := g)
    (hfactor := residueFactor g hfactor)
    (hq := residueAlgebraMap_surjective (R := R))
    (π := π)
    (hπ := residueElement_eq_zero π hπ)
    (hg := hg)
    (hker := hker)

@[simp] theorem residueLinearEquiv_tmul
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap (IsLocalRing.ResidueField R) C).comp (IsLocalRing.residue R))
    (π : R)
    (hπ : π ∈ IsLocalRing.maximalIdeal R)
    (hg : Function.Surjective g)
    (hker :
      RingHom.ker g =
        Ideal.span ({algebraMap R B π} : Set B))
    (a : (IsLocalRing.ResidueField R)) (b : B) :
    residueLinearEquiv g hfactor π hπ hg hker
        (a ⊗ₜ[R] b) =
      a • g b := by
  exact
    tensorLinearEquiv_tmul
      (g := g)
      (hfactor := residueFactor g hfactor)
      (hq := residueAlgebraMap_surjective (R := R))
      (π := π)
      (hπ := residueElement_eq_zero π hπ)
      (hg := hg)
      (hker := hker)
      a b

end ResidueField

section BasisTransport

variable {ι : Type uι}

/-- Pull a target basis back through the special-fibre equivalence. -/
def pullbackBasis
    (e : k ⊗[R] B ≃ₗ[k] C)
    (bC : Basis ι k C) :
    Basis ι k (k ⊗[R] B) :=
  bC.map e.symm

@[simp] theorem pullbackBasis_apply
    (e : k ⊗[R] B ≃ₗ[k] C)
    (bC : Basis ι k C)
    (i : ι) :
    pullbackBasis e bC i = e.symm (bC i) := by
  simp [pullbackBasis]

theorem mk_eq_pullbackBasis
    (e : k ⊗[R] B ≃ₗ[k] C)
    (v : ι → B)
    (bC : Basis ι k C)
    (heval :
      ∀ i : ι,
        e (TensorProduct.mk R k B 1 (v i)) = bC i) :
    ∀ i : ι,
      TensorProduct.mk R k B 1 (v i) =
        pullbackBasis e bC i := by
  intro i
  apply e.injective
  simpa [pullbackBasis] using heval i

end BasisTransport

end

end MazurProof.N13TensorSpecialFiber

end
end

-- module FLT.Assumptions.MazurProof.N13TwoFiberNoEscape
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoFiberNoEscape =====
section

/-!
# Excluding denominator escape from two literal fibres

Let `B` be a torsion-free algebra over a domain `R`, with uniformizer
`π`.  Suppose two elements `e₀,e₁` reduce to a basis of a quotient over
`k = R/(π)`.  If every element of `B` can be brought into the span of
`e₀,e₁` after multiplication by some power of `π`, then it was already
in that span.

The proof removes one factor of `π` at a time.  Reduction modulo `π`
forces both coefficients to be divisible by `π`, and torsion-freeness
cancels the common factor.  This is the algebraic two-fibre no-escape
argument; it uses neither a finite presentation nor a valuation table.
-/

open Module

namespace MazurProof.N13TwoFiberNoEscape

noncomputable section

universe uR uk uB uC

variable {R : Type uR} {k : Type uk}
variable {B : Type uB} {C : Type uC}
variable [CommRing R] [IsDomain R]
variable [Field k]
variable [CommRing B] [CommRing C]
variable [Algebra R k] [Algebra R B] [Algebra R C]
variable [Algebra k C] [IsScalarTower R k C]
variable [Module.IsTorsionFree R B]

/-- The literal ordered pair used on both fibres. -/
def pairFamily (e₀ e₁ : B) : Fin 2 → B :=
  ![e₀, e₁]

@[simp] theorem pairFamily_zero (e₀ e₁ : B) :
    pairFamily e₀ e₁ (0 : Fin 2) = e₀ := by
  simp [pairFamily]

@[simp] theorem pairFamily_one (e₀ e₁ : B) :
    pairFamily e₀ e₁ (1 : Fin 2) = e₁ := by
  simp [pairFamily]

theorem range_pairFamily (e₀ e₁ : B) :
    Set.range (pairFamily e₀ e₁) = {e₀, e₁} := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

/--
One factor of the uniformizer can be removed from a two-generator
relation whose reductions form a basis.
-/
theorem cancel_uniformizer_of_reduced_basis
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k))
    (π : R)
    (hπ_ne : π ≠ 0)
    (hπ_zero : algebraMap R k π = 0)
    (hker :
      RingHom.ker (algebraMap R k) =
        Ideal.span ({π} : Set R))
    (e₀ e₁ : B)
    (bC : Basis (Fin 2) k C)
    (he₀ : g e₀ = bC 0)
    (he₁ : g e₁ = bC 1)
    (z : B) (a₀ a₁ : R)
    (hz :
      π • z = a₀ • e₀ + a₁ • e₁) :
    ∃ c₀ c₁ : R,
      z = c₀ • e₀ + c₁ • e₁ := by
  have hgscalar (a : R) :
      g (algebraMap R B a) = algebraMap R C a := by
    calc
      g (algebraMap R B a) =
          algebraMap k C (algebraMap R k a) := by
        simpa only [RingHom.comp_apply] using
          DFunLike.congr_fun hfactor a
      _ = algebraMap R C a :=
        (IsScalarTower.algebraMap_apply R k C a).symm
  have hred :
      algebraMap R k a₀ • bC 0 +
          algebraMap R k a₁ • bC 1 = 0 := by
    calc
      algebraMap R k a₀ • bC 0 +
            algebraMap R k a₁ • bC 1 =
          g (a₀ • e₀ + a₁ • e₁) := by
            simp only [Algebra.smul_def, map_add, map_mul,
              he₀, he₁]
            rw [hgscalar a₀, hgscalar a₁]
            simp only [← IsScalarTower.algebraMap_apply R k C]
      _ = g (π • z) := congrArg g hz.symm
      _ = 0 := by
        simp only [Algebra.smul_def, map_mul]
        have hscalar :
            g (algebraMap R B π) =
              algebraMap k C (algebraMap R k π) := by
          simpa only [RingHom.comp_apply] using
            DFunLike.congr_fun hfactor π
        rw [hscalar, hπ_zero, map_zero, zero_mul]
  have ha₀ : algebraMap R k a₀ = 0 := by
    have hcoord :=
      congrArg (bC.coord (0 : Fin 2)) hred
    simp only [map_add, map_smul, map_zero,
      Basis.coord_apply, Basis.repr_self_apply] at hcoord
    simpa using hcoord
  have ha₁ : algebraMap R k a₁ = 0 := by
    have hcoord :=
      congrArg (bC.coord (1 : Fin 2)) hred
    simp only [map_add, map_smul, map_zero,
      Basis.coord_apply, Basis.repr_self_apply] at hcoord
    simpa using hcoord
  have ha₀_mem : a₀ ∈ Ideal.span ({π} : Set R) := by
    rw [← hker]
    exact RingHom.mem_ker.mpr ha₀
  have ha₁_mem : a₁ ∈ Ideal.span ({π} : Set R) := by
    rw [← hker]
    exact RingHom.mem_ker.mpr ha₁
  obtain ⟨c₀, hc₀⟩ := Ideal.mem_span_singleton.mp ha₀_mem
  obtain ⟨c₁, hc₁⟩ := Ideal.mem_span_singleton.mp ha₁_mem
  refine ⟨c₀, c₁, ?_⟩
  apply (smul_right_injective (M := B) hπ_ne)
  change π • z = π • (c₀ • e₀ + c₁ • e₁)
  rw [hz, hc₀, hc₁]
  simp only [mul_smul, smul_add]

/--
Iterating the one-step cancellation removes every power of `π`.
-/
theorem exists_pair_of_power_relation
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k))
    (π : R)
    (hπ_ne : π ≠ 0)
    (hπ_zero : algebraMap R k π = 0)
    (hker :
      RingHom.ker (algebraMap R k) =
        Ideal.span ({π} : Set R))
    (e₀ e₁ : B)
    (bC : Basis (Fin 2) k C)
    (he₀ : g e₀ = bC 0)
    (he₁ : g e₁ = bC 1)
    (z : B)
    (hclear :
      ∃ n : ℕ, ∃ a₀ a₁ : R,
        (π ^ n) • z = a₀ • e₀ + a₁ • e₁) :
    ∃ a₀ a₁ : R,
      z = a₀ • e₀ + a₁ • e₁ := by
  obtain ⟨n, a₀, a₁, hz⟩ := hclear
  induction n generalizing z a₀ a₁ with
  | zero =>
      exact ⟨a₀, a₁, by simpa using hz⟩
  | succ n ih =>
      have hstep :
          π • ((π ^ n) • z) =
            a₀ • e₀ + a₁ • e₁ := by
        simpa only [pow_succ', mul_smul] using hz
      obtain ⟨c₀, c₁, hc⟩ :=
        cancel_uniformizer_of_reduced_basis
          g hfactor π hπ_ne hπ_zero hker
          e₀ e₁ bC he₀ he₁
          ((π ^ n) • z) a₀ a₁ hstep
      exact ih (z := z) (a₀ := c₀) (a₁ := c₁) hc

/--
The power-clearing hypothesis and a basis on the reduced fibre force the
two elements to span the entire integral algebra.
-/
theorem span_pair_eq_top
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k))
    (π : R)
    (hπ_ne : π ≠ 0)
    (hπ_zero : algebraMap R k π = 0)
    (hker :
      RingHom.ker (algebraMap R k) =
        Ideal.span ({π} : Set R))
    (e₀ e₁ : B)
    (bC : Basis (Fin 2) k C)
    (he₀ : g e₀ = bC 0)
    (he₁ : g e₁ = bC 1)
    (hclear :
      ∀ z : B, ∃ n : ℕ, ∃ a₀ a₁ : R,
        (π ^ n) • z = a₀ • e₀ + a₁ • e₁) :
    Submodule.span R ({e₀, e₁} : Set B) = ⊤ := by
  rw [eq_top_iff]
  intro z
  intro _
  obtain ⟨a₀, a₁, hz⟩ :=
    exists_pair_of_power_relation
      g hfactor π hπ_ne hπ_zero hker
      e₀ e₁ bC he₀ he₁ z (hclear z)
  rw [hz]
  exact Submodule.add_mem _
    (Submodule.smul_mem _
      a₀ (Submodule.subset_span (Set.mem_insert e₀ {e₁})))
    (Submodule.smul_mem _
      a₁ (Submodule.subset_span
        (Set.mem_insert_iff.mpr
          (Or.inr (Set.mem_singleton e₁)))))

section FractionFieldClearing

universe uK uG

variable {K : Type uK} {G : Type uG}
variable [Field K] [CommRing G]
variable [Algebra R K] [IsFractionRing R K]
variable [Algebra R G] [Algebra K G]
variable [IsScalarTower R K G]

/--
Two coefficients in the fraction field admit one common nonzero
denominator.
-/
theorem exists_common_denominator
    (α₀ α₁ : K) :
    ∃ r : R, r ≠ 0 ∧
      ∃ a₀ a₁ : R,
        algebraMap R K r * α₀ = algebraMap R K a₀ ∧
        algebraMap R K r * α₁ = algebraMap R K a₁ := by
  obtain ⟨b₀, d₀, hd₀, hα₀⟩ :=
    IsFractionRing.div_surjective R α₀
  obtain ⟨b₁, d₁, hd₁, hα₁⟩ :=
    IsFractionRing.div_surjective R α₁
  have hd₀_ne : d₀ ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp hd₀
  have hd₁_ne : d₁ ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp hd₁
  have hmapd₀ : algebraMap R K d₀ ≠ 0 :=
    by simpa using (IsFractionRing.injective R K).ne hd₀_ne
  have hmapd₁ : algebraMap R K d₁ ≠ 0 :=
    by simpa using (IsFractionRing.injective R K).ne hd₁_ne
  refine ⟨d₀ * d₁, mul_ne_zero hd₀_ne hd₁_ne,
    b₀ * d₁, b₁ * d₀, ?_, ?_⟩
  · rw [← hα₀]
    push_cast
    field_simp
  · rw [← hα₁]
    push_cast
    field_simp

/--
A two-generator generic-fibre presentation clears to one integral
relation with an arbitrary nonzero scalar denominator.
-/
theorem exists_scalar_relation_of_fraction_pair
    (q : B →+* G)
    (hfactor :
      q.comp (algebraMap R B) = algebraMap R G)
    (hq : Function.Injective q)
    (e₀ e₁ z : B)
    (hgeneric :
      ∃ α₀ α₁ : K,
        q z = α₀ • q e₀ + α₁ • q e₁) :
    ∃ r : R, r ≠ 0 ∧
      ∃ a₀ a₁ : R,
        r • z = a₀ • e₀ + a₁ • e₁ := by
  obtain ⟨α₀, α₁, hz⟩ := hgeneric
  obtain ⟨r, hr, a₀, a₁, ha₀, ha₁⟩ :=
    exists_common_denominator (R := R) α₀ α₁
  refine ⟨r, hr, a₀, a₁, hq ?_⟩
  have hqscalar (a : R) :
      q (algebraMap R B a) = algebraMap R G a := by
    simpa only [RingHom.comp_apply] using
      DFunLike.congr_fun hfactor a
  calc
    q (r • z) =
        algebraMap R G r * q z := by
      simp only [Algebra.smul_def, map_mul, hqscalar]
    _ =
        algebraMap K G (algebraMap R K r) *
          (α₀ • q e₀ + α₁ • q e₁) := by
      rw [hz, IsScalarTower.algebraMap_apply R K G]
    _ =
        (algebraMap R K r * α₀) • q e₀ +
          (algebraMap R K r * α₁) • q e₁ := by
      simp only [Algebra.smul_def, mul_add, map_mul]
      ring
    _ =
        algebraMap R K a₀ • q e₀ +
          algebraMap R K a₁ • q e₁ := by
      rw [ha₀, ha₁]
    _ =
        q (a₀ • e₀ + a₁ • e₁) := by
      simp only [Algebra.smul_def, map_add, map_mul, hqscalar,
        IsScalarTower.algebraMap_apply R K G]

/--
Over a discrete valuation ring, the arbitrary denominator can be replaced
by a power of any chosen uniformizer.
-/
theorem exists_power_relation_of_fraction_pair
    [IsDiscreteValuationRing R]
    (π : R)
    (hπ : Irreducible π)
    (q : B →+* G)
    (hfactor :
      q.comp (algebraMap R B) = algebraMap R G)
    (hq : Function.Injective q)
    (e₀ e₁ z : B)
    (hgeneric :
      ∃ α₀ α₁ : K,
        q z = α₀ • q e₀ + α₁ • q e₁) :
    ∃ n : ℕ, ∃ a₀ a₁ : R,
      (π ^ n) • z = a₀ • e₀ + a₁ • e₁ := by
  obtain ⟨r, hr, a₀, a₁, hz⟩ :=
    exists_scalar_relation_of_fraction_pair
      (R := R) (K := K) q hfactor hq e₀ e₁ z hgeneric
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      hr hπ
  refine
    ⟨n, (↑(u⁻¹) : R) * a₀, (↑(u⁻¹) : R) * a₁, ?_⟩
  apply (smul_right_injective (M := B) u.ne_zero)
  change
    (u : R) • ((π ^ n) • z) =
      (u : R) •
        (((↑(u⁻¹) : R) * a₀) • e₀ +
          ((↑(u⁻¹) : R) * a₁) • e₁)
  rw [← mul_smul, ← hu, hz]
  simp only [smul_add, ← mul_smul]
  norm_num

/--
The generic basis gives the required two-coefficient presentation of every
generic image.
-/
theorem exists_generic_pair_of_basis
    (q : B →+* G)
    (e₀ e₁ z : B)
    (bG : Basis (Fin 2) K G)
    (he₀ : q e₀ = bG 0)
    (he₁ : q e₁ = bG 1) :
    ∃ α₀ α₁ : K,
      q z = α₀ • q e₀ + α₁ • q e₁ := by
  refine
    ⟨bG.repr (q z) 0, bG.repr (q z) 1, ?_⟩
  have hsum := bG.sum_repr (q z)
  rw [Fin.sum_univ_two] at hsum
  rw [he₀, he₁]
  exact hsum.symm

/--
An injective generic-fibre map carrying the pair to a basis proves
integral linear independence of the same pair.
-/
theorem pair_linearIndependent_of_fraction_basis
    (q : B →+* G)
    (hfactor :
      q.comp (algebraMap R B) = algebraMap R G)
    (hq : Function.Injective q)
    (e₀ e₁ : B)
    (bG : Basis (Fin 2) K G)
    (he₀ : q e₀ = bG 0)
    (he₁ : q e₁ = bG 1) :
    LinearIndependent R (pairFamily e₀ e₁) := by
  let qAlg : B →ₐ[R] G :=
    { toRingHom := q
      commutes' := fun a => by
        change q (algebraMap R B a) = algebraMap R G a
        simpa only [RingHom.comp_apply] using
          DFunLike.congr_fun hfactor a }
  have hmap :
      qAlg.toLinearMap ∘ pairFamily e₀ e₁ =
        (bG : Fin 2 → G) := by
    funext i
    fin_cases i
    · exact he₀
    · exact he₁
  have hliMap :
      LinearIndependent R
        (qAlg.toLinearMap ∘ pairFamily e₀ e₁) := by
    rw [hmap]
    exact bG.linearIndependent.restrict_scalars' R
  exact
    (qAlg.toLinearMap.linearIndependent_iff
      (LinearMap.ker_eq_bot.mpr hq)).mp hliMap

/--
The two-fibre argument in one statement: a generic basis clears
denominators, the reduced basis removes them, and generic injectivity gives
linear independence.  Hence the same literal pair is an integral basis.
-/
theorem exists_basis_of_two_fibres
    [IsDiscreteValuationRing R]
    (π : R)
    (hπ : Irreducible π)
    (g : B →+* C)
    (hfactorSpecial :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k))
    (hπ_zero : algebraMap R k π = 0)
    (hkerSpecial :
      RingHom.ker (algebraMap R k) =
        Ideal.span ({π} : Set R))
    (q : B →+* G)
    (hfactorGeneric :
      q.comp (algebraMap R B) = algebraMap R G)
    (hq : Function.Injective q)
    (e₀ e₁ : B)
    (bC : Basis (Fin 2) k C)
    (hg₀ : g e₀ = bC 0)
    (hg₁ : g e₁ = bC 1)
    (bG : Basis (Fin 2) K G)
    (hq₀ : q e₀ = bG 0)
    (hq₁ : q e₁ = bG 1) :
    ∃ b : Basis (Fin 2) R B,
      (b : Fin 2 → B) = pairFamily e₀ e₁ := by
  have hπ_ne : π ≠ 0 := hπ.ne_zero
  have hclear :
      ∀ z : B, ∃ n : ℕ, ∃ a₀ a₁ : R,
        (π ^ n) • z = a₀ • e₀ + a₁ • e₁ := by
    intro z
    exact
      exists_power_relation_of_fraction_pair
        (R := R) (K := K) π hπ q hfactorGeneric hq
        e₀ e₁ z
        (exists_generic_pair_of_basis q e₀ e₁ z
          bG hq₀ hq₁)
  have hspanPair :
      Submodule.span R ({e₀, e₁} : Set B) = ⊤ :=
    span_pair_eq_top
      g hfactorSpecial π hπ_ne hπ_zero hkerSpecial
      e₀ e₁ bC hg₀ hg₁ hclear
  have hspan :
      Submodule.span R
          (Set.range (pairFamily e₀ e₁)) = ⊤ := by
    rw [range_pairFamily]
    exact hspanPair
  have hli :
      LinearIndependent R (pairFamily e₀ e₁) :=
    pair_linearIndependent_of_fraction_basis
      (R := R) (K := K)
      q hfactorGeneric hq e₀ e₁ bG hq₀ hq₁
  exact
    ⟨Basis.mk hli hspan.ge, Basis.coe_mk hli hspan.ge⟩

end FractionFieldClearing

end

end MazurProof.N13TwoFiberNoEscape

end
end


