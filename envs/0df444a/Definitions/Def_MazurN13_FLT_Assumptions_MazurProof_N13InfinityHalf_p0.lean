-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityHalf_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13InfinityHalf_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:26:41.859643+00:00
-- url     : https://prove2.me/theorems/dd5798ce-ab84-4995-a300-f100609f0f4c
-- title:
--   FLT.Assumptions.MazurProof.N13InfinityHalf source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13InfinityHalf

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13InfinityHalf
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianFactorization_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordAbelJacobi_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13BranchNorm_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13BranchLeading_p0

set_option autoImplicit false




/-!
# A half of the infinity-difference class on the N13 sextic

The Gaussian factorization `f = A² + B²` supplies a balanced Mumford pair
`u = X(X+1)`, `v = -(2X+1)` and the function `g = Y-A`.  We prove

`(u, Y-v)² = (g)` and `ord_{∞₊}(g) = -1`.

The corresponding oriented Picard identity says that this Mumford class
doubles to the difference of the two points at infinity.  This removes the
extra even-degree ambiguity in the fake 2-Kummer kernel.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13InfinityHalf

noncomputable section

open SexticMumford

abbrev M := N13Mumford.model ℚ

def halfU : ℚ[X] := X * (X + 1)

def halfV : ℚ[X] := -(2 * X + 1)

theorem halfU_monic : halfU.Monic := by
  unfold halfU
  monicity!

theorem halfU_natDegree : halfU.natDegree = 2 := by
  unfold halfU
  compute_degree!

theorem half_curve_factor :
    N13Mumford.f ℚ - halfV ^ 2 =
      halfU * (X ^ 4 + 3 * X ^ 3 + 3 * X ^ 2 - X - 2) := by
  simp [N13Mumford.f, halfU, halfV]
  ring

def infinityHalf : Mumford M where
  u := halfU
  v := halfV
  nInf := 0
  u_monic := halfU_monic
  deg_u := halfU_natDegree.le
  v_reduced := by
    rw [mod_eq_self_iff halfU_monic.ne_zero]
    have hv : halfV.natDegree = 1 := by
      unfold halfV
      compute_degree!
      all_goals norm_num [Polynomial.coeff_one]
    rw [degree_eq_natDegree (by
      intro h
      have := congrArg (fun p : ℚ[X] => p.coeff 1) h
      norm_num [halfV, Polynomial.coeff_one] at this),
      degree_eq_natDegree halfU_monic.ne_zero,
      hv, halfU_natDegree]
    norm_num
  curve_dvd := by
    exact ⟨X ^ 4 + 3 * X ^ 3 + 3 * X ^ 2 - X - 2,
      half_curve_factor⟩
  infinity_bound := by simp [halfU_natDegree]

def halfFunction : N13Mumford.CoordinateRing ℚ :=
  N13BranchNorm.linearFunction ℚ (-N13GaussianFactorization.A) 1

theorem halfFunction_norm :
    norm M halfFunction = xClass M (-4 * halfU ^ 2) := by
  rw [show halfFunction =
      xClass M (-N13GaussianFactorization.A) +
        xClass M 1 * yClass M by rfl]
  rw [norm_recompose]
  congr 1
  change (-N13GaussianFactorization.A) ^ 2 -
      1 ^ 2 * N13Mumford.f ℚ = -4 * halfU ^ 2
  rw [N13GaussianFactorization.f_eq_sum_squares]
  simp [N13GaussianFactorization.B, halfU]
  ring

theorem linearFunction_mul (p q r s : ℚ[X]) :
    N13BranchNorm.linearFunction ℚ p q *
        N13BranchNorm.linearFunction ℚ r s =
      N13BranchNorm.linearFunction ℚ
        (p * r + q * s * N13Mumford.f ℚ)
        (p * s + q * r) := by
  simp only [N13BranchNorm.linearFunction]
  calc
    (xClass M p + xClass M q * yClass M) *
          (xClass M r + xClass M s * yClass M) =
        xClass M p * xClass M r +
          (xClass M p * xClass M s +
            xClass M q * xClass M r) * yClass M +
          xClass M q * xClass M s * yClass M ^ 2 := by ring
    _ = xClass M p * xClass M r +
          (xClass M p * xClass M s +
            xClass M q * xClass M r) * yClass M +
          xClass M q * xClass M s * xClass M (N13Mumford.f ℚ) := by
            rw [show yClass M ^ 2 =
              xClass M (N13Mumford.f ℚ) by
                simpa [M] using yClass_sq M]
    _ = _ := by
      change
        xClass M p * xClass M r +
              (xClass M p * xClass M s +
                xClass M q * xClass M r) * yClass M +
              xClass M q * xClass M s *
                xClass M (N13Mumford.f ℚ) =
          xClass M (p * r + q * s * N13Mumford.f ℚ) +
            xClass M (p * s + q * r) * yClass M
      simp only [xClass_add, xClass_mul]
      ring

theorem four_mul_quarter :
    (4 : ℚ[X]) * C ((4 : ℚ)⁻¹) = 1 := by
  calc
    (4 : ℚ[X]) * C ((4 : ℚ)⁻¹) =
        C (4 : ℚ) * C ((4 : ℚ)⁻¹) := by rw [Polynomial.C_ofNat]
    _ = C ((4 : ℚ) * (4 : ℚ)⁻¹) := by rw [C_mul]
    _ = 1 := by norm_num

theorem two_mul_half :
    (2 : ℚ[X]) * C ((2 : ℚ)⁻¹) = 1 := by
  calc
    (2 : ℚ[X]) * C ((2 : ℚ)⁻¹) =
        C (2 : ℚ) * C ((2 : ℚ)⁻¹) := by rw [Polynomial.C_ofNat]
    _ = C ((2 : ℚ) * (2 : ℚ)⁻¹) := by rw [C_mul]
    _ = 1 := by norm_num

def halfA2Factor : N13Mumford.CoordinateRing ℚ :=
  N13BranchNorm.linearFunction ℚ
    (C ((4 : ℚ)⁻¹) * N13GaussianFactorization.A) (C ((4 : ℚ)⁻¹))

def halfABFactor : N13Mumford.CoordinateRing ℚ :=
  N13BranchNorm.linearFunction ℚ
    (halfU + N13GaussianFactorization.A *
      (C ((4 : ℚ)⁻¹) * (X + 1)))
    (C ((4 : ℚ)⁻¹) * (X + 1))

def halfB2Q : ℚ[X] :=
  C ((4 : ℚ)⁻¹) * (4 + (X + 1) ^ 2)

def halfB2Factor : N13Mumford.CoordinateRing ℚ :=
  N13BranchNorm.linearFunction ℚ
    (-2 * halfV + N13GaussianFactorization.A * halfB2Q)
    halfB2Q

theorem halfFunction_mul_halfA2Factor :
    halfFunction * halfA2Factor = xClass M (halfU ^ 2) := by
  rw [halfFunction, halfA2Factor, linearFunction_mul]
  rw [N13GaussianFactorization.f_eq_sum_squares]
  have h0 :
      (-N13GaussianFactorization.A) *
            (C ((4 : ℚ)⁻¹) * N13GaussianFactorization.A) +
          1 * C ((4 : ℚ)⁻¹) *
            (N13GaussianFactorization.A ^ 2 +
              N13GaussianFactorization.B ^ 2) =
        halfU ^ 2 := by
    simp [N13GaussianFactorization.B, halfU]
    linear_combination
      (X ^ 2 + 2 * X ^ 3 + X ^ 4) * four_mul_quarter
  have h1 :
      (-N13GaussianFactorization.A) * C ((4 : ℚ)⁻¹) +
          1 * (C ((4 : ℚ)⁻¹) * N13GaussianFactorization.A) = 0 := by ring
  rw [h0, h1]
  simp [N13BranchNorm.linearFunction]

theorem halfFunction_mul_halfABFactor :
    halfFunction * halfABFactor =
      xClass M halfU * ySubClass M halfV := by
  rw [halfFunction, halfABFactor, linearFunction_mul]
  have h0 :
      (-N13GaussianFactorization.A) *
            (halfU + N13GaussianFactorization.A *
              (C ((4 : ℚ)⁻¹) * (X + 1))) +
          1 * (C ((4 : ℚ)⁻¹) * (X + 1)) * N13Mumford.f ℚ =
        halfU * (-halfV) := by
    simp [N13GaussianFactorization.A, N13Mumford.f, halfU, halfV]
    linear_combination
      (X ^ 2 + 3 * X ^ 3 + 3 * X ^ 4 + X ^ 5) *
        four_mul_quarter
  have h1 :
      (-N13GaussianFactorization.A) *
          (C ((4 : ℚ)⁻¹) * (X + 1)) +
          1 * (halfU +
            N13GaussianFactorization.A *
              (C ((4 : ℚ)⁻¹) * (X + 1))) =
        halfU := by
    ring
  rw [h0, h1]
  simp [N13BranchNorm.linearFunction, ySubClass]
  ring

theorem halfFunction_mul_halfB2Factor :
    halfFunction * halfB2Factor =
      ySubClass M halfV * ySubClass M halfV := by
  rw [halfFunction, halfB2Factor, linearFunction_mul]
  have h0 :
      (-N13GaussianFactorization.A) *
            (-2 * halfV +
              N13GaussianFactorization.A * halfB2Q) +
          1 * halfB2Q * N13Mumford.f ℚ =
        N13Mumford.f ℚ + halfV ^ 2 := by
    simp [N13GaussianFactorization.A, N13Mumford.f, halfV, halfB2Q]
    linear_combination
      (5 * X ^ 2 + 12 * X ^ 3 + 10 * X ^ 4 +
        4 * X ^ 5 + X ^ 6) * four_mul_quarter
  have h1 :
      (-N13GaussianFactorization.A) * halfB2Q +
          1 * (-2 * halfV +
            N13GaussianFactorization.A * halfB2Q) =
        -2 * halfV := by ring
  rw [h0, h1]
  simp [N13BranchNorm.linearFunction, ySubClass]
  rw [show xClass M (N13Mumford.f ℚ) = yClass M ^ 2 by
    simpa [M] using (yClass_sq M).symm]
  have hc2 : xClass M (2 : ℚ[X]) = 2 := by
    change xClassHom M (2 : ℚ[X]) = 2
    exact map_ofNat (xClassHom M) 2
  rw [hc2]
  ring

def backP : ℚ[X] :=
  -(C ((2 : ℚ)⁻¹) *
    (2 * X ^ 3 + 5 * X ^ 2 + 4 * X - 3))

def backQ : ℚ[X] := -4

def backR : ℚ[X] := X + C ((2 : ℚ)⁻¹)

theorem halfFunction_back_combination :
    halfFunction =
      xClass M backP * (xClass M halfU * xClass M halfU) +
      xClass M backQ *
        (xClass M halfU * ySubClass M halfV) +
      xClass M backR *
        (ySubClass M halfV * ySubClass M halfV) := by
  simp only [halfFunction, N13BranchNorm.linearFunction, ySubClass]
  calc
    xClass M (-N13GaussianFactorization.A) +
        xClass M 1 * yClass M =
      xClass M
          (backP * halfU ^ 2 +
            backQ * (-halfU * halfV) +
            backR * (N13Mumford.f ℚ + halfV ^ 2)) +
        xClass M
          (backQ * halfU + backR * (-2 * halfV)) *
          yClass M := by
      have h0 :
          backP * halfU ^ 2 +
              backQ * (-halfU * halfV) +
              backR * (N13Mumford.f ℚ + halfV ^ 2) =
            -N13GaussianFactorization.A := by
        simp [N13GaussianFactorization.A, N13Mumford.f, halfU, halfV,
          backP, backQ, backR]
        linear_combination
          (1 + 3 * X + 4 * X ^ 2 + 2 * X ^ 3 -
            2 * X ^ 4 - 6 * X ^ 5 - 4 * X ^ 6 - X ^ 7) *
              two_mul_half
      have h1 :
          backQ * halfU + backR * (-2 * halfV) = 1 := by
        simp [halfU, halfV, backQ, backR]
        linear_combination (2 * X + 1) * two_mul_half
      rw [h0, h1]
    _ = _ := by
      simp only [xClass_add, xClass_mul, xClass_pow, xClass_neg]
      rw [show xClass M (N13Mumford.f ℚ) = yClass M ^ 2 by
        simpa [M] using (yClass_sq M).symm]
      have hc2 : xClass M (2 : ℚ[X]) = 2 := by
        change xClassHom M (2 : ℚ[X]) = 2
        exact map_ofNat (xClassHom M) 2
      rw [hc2]
      ring

theorem halfFunction_mem_ideal_sq :
    halfFunction ∈
      mumfordIdeal M halfU halfV * mumfordIdeal M halfU halfV := by
  let a := xClass M halfU
  let b := ySubClass M halfV
  have ha : a ∈ mumfordIdeal M halfU halfV :=
    xClass_mem_mumfordIdeal M halfU halfV
  have hb : b ∈ mumfordIdeal M halfU halfV :=
    ySubClass_mem_mumfordIdeal M halfU halfV
  have haa : a * a ∈
      mumfordIdeal M halfU halfV * mumfordIdeal M halfU halfV :=
    Ideal.mul_mem_mul ha ha
  have hab : a * b ∈
      mumfordIdeal M halfU halfV * mumfordIdeal M halfU halfV :=
    Ideal.mul_mem_mul ha hb
  have hbb : b * b ∈
      mumfordIdeal M halfU halfV * mumfordIdeal M halfU halfV :=
    Ideal.mul_mem_mul hb hb
  have hsum :
      xClass M backP * (a * a) + xClass M backQ * (a * b) +
          xClass M backR * (b * b) ∈
        mumfordIdeal M halfU halfV * mumfordIdeal M halfU halfV :=
    Ideal.add_mem _ (Ideal.add_mem _
      (Ideal.mul_mem_left _ _ haa)
      (Ideal.mul_mem_left _ _ hab))
      (Ideal.mul_mem_left _ _ hbb)
  rw [halfFunction_back_combination]
  exact hsum

theorem ideal_sq_le_halfFunction :
    mumfordIdeal M halfU halfV * mumfordIdeal M halfU halfV ≤
      Ideal.span ({halfFunction} :
        Set (N13Mumford.CoordinateRing ℚ)) := by
  let I := mumfordIdeal M halfU halfV
  let G := Ideal.span ({halfFunction} :
    Set (N13Mumford.CoordinateRing ℚ))
  let a := xClass M halfU
  let b := ySubClass M halfV
  have ha2 : a * a ∈ G := by
    rw [Ideal.mem_span_singleton]
    refine ⟨halfA2Factor, ?_⟩
    rw [mul_comm, halfFunction_mul_halfA2Factor]
    simp [a, pow_two]
  have hab : a * b ∈ G := by
    rw [Ideal.mem_span_singleton]
    refine ⟨halfABFactor, ?_⟩
    rw [mul_comm, halfFunction_mul_halfABFactor]
    simp [a, b, mul_comm]
  have hb2 : b * b ∈ G := by
    rw [Ideal.mem_span_singleton]
    refine ⟨halfB2Factor, ?_⟩
    rw [mul_comm, halfFunction_mul_halfB2Factor]
  apply Ideal.mul_le.mpr
  intro p hp q hq
  obtain ⟨p₀, pY, hpEq⟩ := Ideal.mem_span_pair.mp hp
  obtain ⟨q₀, qY, hqEq⟩ := Ideal.mem_span_pair.mp hq
  have h00 : (p₀ * q₀) * (a * a) ∈ G :=
    Ideal.mul_mem_left G _ ha2
  have h01 : (p₀ * qY) * (a * b) ∈ G :=
    Ideal.mul_mem_left G _ hab
  have h10 : (pY * q₀) * (a * b) ∈ G :=
    Ideal.mul_mem_left G _ hab
  have h11 : (pY * qY) * (b * b) ∈ G :=
    Ideal.mul_mem_left G _ hb2
  have hsum := Ideal.add_mem G
    (Ideal.add_mem G (Ideal.add_mem G h00 h01) h10) h11
  rw [← hpEq, ← hqEq]
  convert hsum using 1
  all_goals ring

theorem halfIdeal_sq :
    mumfordIdeal M halfU halfV * mumfordIdeal M halfU halfV =
      Ideal.span ({halfFunction} :
        Set (N13Mumford.CoordinateRing ℚ)) := by
  apply le_antisymm
  · exact ideal_sq_le_halfFunction
  · rw [Ideal.span_le]
    intro z hz
    simpa only [Set.mem_singleton_iff] using
      hz ▸ halfFunction_mem_ideal_sq

private theorem wSeries_coeff_zero :
    (N13Infinity.wSeries ℚ).coeff (0 : ℤ) = 1 := by
  change (HahnSeries.ofPowerSeries ℤ ℚ
    (N13Infinity.sqrtReverseF ℚ)).coeff (0 : ℕ) = 1
  rw [HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff,
    N13Infinity.sqrtReverseF_constantCoeff]

theorem evalPoly_negA_coeff_neg_three :
    (N13BranchNorm.evalPoly ℚ
      (-N13GaussianFactorization.A)).coeff (-3 : ℤ) = -1 := by
  simp [N13BranchNorm.evalPoly, N13GaussianFactorization.A,
    N13Infinity.parameter]
  change ((2 : LaurentSeries ℚ) *
    HahnSeries.single (-2 : ℤ) 1).coeff (-3 : ℤ) = 0
  rw [show (2 : LaurentSeries ℚ) =
    HahnSeries.single (0 : ℤ) 2 by
      rfl]
  rw [HahnSeries.coeff_single_mul]
  norm_num [HahnSeries.coeff_single]

theorem ySeries_coeff_neg_three :
    (N13Infinity.ySeries ℚ).coeff (-3 : ℤ) = 1 := by
  simp only [N13Infinity.ySeries, N13Infinity.parameter,
    HahnSeries.inv_single, inv_one,
    HahnSeries.single_pow, one_pow]
  rw [HahnSeries.coeff_single_mul]
  norm_num
  exact wSeries_coeff_zero

theorem halfFunction_ne_zero : halfFunction ≠ 0 := by
  intro h
  have hY := congrArg (coeffY M) h
  simp [halfFunction, N13BranchNorm.linearFunction] at hY

theorem half_normNumerator :
    N13BranchNorm.normNumerator ℚ
      (-N13GaussianFactorization.A) 1 = -4 * halfU ^ 2 := by
  simp [N13BranchNorm.normNumerator,
    N13GaussianFactorization.f_eq_sum_squares,
    N13GaussianFactorization.B, halfU]
  ring

theorem half_normNumerator_ne_zero :
    N13BranchNorm.normNumerator ℚ
      (-N13GaussianFactorization.A) 1 ≠ 0 := by
  rw [half_normNumerator]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ halfU_monic.ne_zero)

theorem half_normNumerator_natDegree :
    (N13BranchNorm.normNumerator ℚ
      (-N13GaussianFactorization.A) 1).natDegree = 4 := by
  rw [half_normNumerator]
  compute_degree! <;>
    simp [halfU_natDegree, halfU_monic.ne_zero]

theorem half_poleDegree :
    N13BranchLeading.poleDegree ℚ
      (-N13GaussianFactorization.A) 1 = 3 := by
  simp [N13BranchLeading.poleDegree, N13GaussianFactorization.A]
  compute_degree!

theorem halfFunction_minus_coeff_neg_three :
    (N13InfinityMinus.coordinateToLaurentMinus ℚ
      halfFunction).coeff (-3 : ℤ) = -2 := by
  rw [show halfFunction =
    N13BranchNorm.linearFunction ℚ
      (-N13GaussianFactorization.A) 1 by rfl,
    N13BranchNorm.coordinateToLaurentMinus_linearFunction]
  simp only [map_one, one_mul, HahnSeries.coeff_sub,
    evalPoly_negA_coeff_neg_three, ySeries_coeff_neg_three]
  norm_num

theorem halfFunction_minus_order :
    (N13InfinityMinus.coordinateToLaurentMinus ℚ halfFunction).order =
      -3 := by
  have hmin := N13BranchLeading.branch_min_order ℚ
    (-N13GaussianFactorization.A) 1 halfFunction_ne_zero
  change min
      (N13Infinity.coordinateToLaurent ℚ halfFunction).order
      (N13InfinityMinus.coordinateToLaurentMinus ℚ halfFunction).order =
    -(N13BranchLeading.poleDegree ℚ
      (-N13GaussianFactorization.A) 1 : ℤ) at hmin
  rw [half_poleDegree] at hmin
  have hlower : (-3 : ℤ) ≤
      (N13InfinityMinus.coordinateToLaurentMinus ℚ halfFunction).order := by
    omega
  have hupper :
      (N13InfinityMinus.coordinateToLaurentMinus ℚ halfFunction).order ≤
        (-3 : ℤ) :=
    HahnSeries.order_le_of_coeff_ne_zero (by
      rw [halfFunction_minus_coeff_neg_three]
      norm_num)
  exact le_antisymm hupper hlower

theorem halfFunction_plus_order :
    (N13Infinity.coordinateToLaurent ℚ halfFunction).order = -1 := by
  have hsum := N13BranchNorm.branch_orders_add ℚ
    (-N13GaussianFactorization.A) 1 half_normNumerator_ne_zero
  rw [half_normNumerator_natDegree] at hsum
  change
    (N13Infinity.coordinateToLaurent ℚ halfFunction).order +
        (N13InfinityMinus.coordinateToLaurentMinus ℚ halfFunction).order =
      -(4 : ℤ) at hsum
  rw [halfFunction_minus_order] at hsum
  omega

def halfFunctionUnit : (N13Mumford.FunctionField ℚ)ˣ :=
  Units.mk0
    (algebraMap (N13Mumford.CoordinateRing ℚ)
      (N13Mumford.FunctionField ℚ) halfFunction)
    (by simpa using (IsFractionRing.injective
      (N13Mumford.CoordinateRing ℚ)
      (N13Mumford.FunctionField ℚ)).ne halfFunction_ne_zero)

theorem ordPlus_halfFunctionUnit :
    (N13Infinity.positiveInfinityOrder ℚ).ordPlus halfFunctionUnit =
      Multiplicative.ofAdd (-1 : ℤ) := by
  change Multiplicative.ofAdd
      ((N13Infinity.functionFieldToLaurent ℚ
        (algebraMap (N13Mumford.CoordinateRing ℚ)
          (N13Mumford.FunctionField ℚ) halfFunction)).order) =
    Multiplicative.ofAdd (-1 : ℤ)
  rw [N13Infinity.functionFieldToLaurent_algebraMap]
  exact congrArg Multiplicative.ofAdd halfFunction_plus_order

theorem halfIdealUnit_sq :
    mumfordIdealUnit M infinityHalf.toSemi ^ 2 =
      toPrincipalIdeal
        (N13Mumford.CoordinateRing ℚ)
        (N13Mumford.FunctionField ℚ) halfFunctionUnit := by
  apply Units.ext
  change
    ((mumfordIdealUnit M infinityHalf.toSemi :
        (FractionalIdeal (N13Mumford.CoordinateRing ℚ)⁰
          (N13Mumford.FunctionField ℚ))ˣ) :
      FractionalIdeal (N13Mumford.CoordinateRing ℚ)⁰
        (N13Mumford.FunctionField ℚ)) ^
      2 =
    ((toPrincipalIdeal
        (N13Mumford.CoordinateRing ℚ)
        (N13Mumford.FunctionField ℚ) halfFunctionUnit :
          (FractionalIdeal (N13Mumford.CoordinateRing ℚ)⁰
            (N13Mumford.FunctionField ℚ))ˣ) :
        FractionalIdeal (N13Mumford.CoordinateRing ℚ)⁰
          (N13Mumford.FunctionField ℚ))
  rw [coe_mumfordIdealUnit, coe_toPrincipalIdeal]
  change
    (mumfordIdeal M halfU halfV :
      FractionalIdeal (N13Mumford.CoordinateRing ℚ)⁰
        (N13Mumford.FunctionField ℚ)) ^ 2 =
      FractionalIdeal.spanSingleton
        (N13Mumford.CoordinateRing ℚ)⁰
        (algebraMap (N13Mumford.CoordinateRing ℚ)
          (N13Mumford.FunctionField ℚ) halfFunction)
  rw [pow_two, ← FractionalIdeal.coeIdeal_mul, halfIdeal_sq,
    FractionalIdeal.coeIdeal_span_singleton]

theorem mumfordRaw_infinityHalf_sq :
    mumfordRaw M infinityHalf * mumfordRaw M infinityHalf =
      principalOriented M (N13Infinity.positiveInfinityOrder ℚ)
          halfFunctionUnit *
        mumfordRaw M (infinityMinusMumford M) := by
  apply Prod.ext
  · change
      mumfordIdealUnit M infinityHalf.toSemi *
          mumfordIdealUnit M infinityHalf.toSemi =
        toPrincipalIdeal
            (N13Mumford.CoordinateRing ℚ)
            (N13Mumford.FunctionField ℚ) halfFunctionUnit *
          mumfordIdealUnit M (infinityMinusMumford M).toSemi
    rw [← pow_two, halfIdealUnit_sq]
    have hinf :
        mumfordIdealUnit M (infinityMinusMumford M).toSemi = 1 := by
      change mumfordIdealUnit M (zero M).toSemi = 1
      exact mumfordIdealUnit_zero M
    rw [hinf, mul_one]
  · change
      Multiplicative.ofAdd ((infinityHalf.nInf : ℤ) - 1) *
          Multiplicative.ofAdd ((infinityHalf.nInf : ℤ) - 1) =
        (N13Infinity.positiveInfinityOrder ℚ).ordPlus halfFunctionUnit *
          Multiplicative.ofAdd
            (((infinityMinusMumford M).nInf : ℤ) - 1)
    rw [ordPlus_halfFunctionUnit]
    norm_num [infinityHalf, infinityMinusMumford]

theorem two_nsmul_classOf_infinityHalf :
    2 • classOf M (N13Infinity.positiveInfinityOrder ℚ) infinityHalf =
      classOf M (N13Infinity.positiveInfinityOrder ℚ)
        (infinityMinusMumford M) := by
  rw [two_nsmul]
  change
    Additive.ofMul
        (QuotientGroup.mk'
          (principalOriented M
            (N13Infinity.positiveInfinityOrder ℚ)).range
          (mumfordRaw M infinityHalf)) +
      Additive.ofMul
        (QuotientGroup.mk'
          (principalOriented M
            (N13Infinity.positiveInfinityOrder ℚ)).range
          (mumfordRaw M infinityHalf)) =
    Additive.ofMul
      (QuotientGroup.mk'
        (principalOriented M
          (N13Infinity.positiveInfinityOrder ℚ)).range
        (mumfordRaw M (infinityMinusMumford M)))
  change
    Additive.ofMul
      (QuotientGroup.mk'
          (principalOriented M
            (N13Infinity.positiveInfinityOrder ℚ)).range
          (mumfordRaw M infinityHalf) *
        QuotientGroup.mk'
          (principalOriented M
            (N13Infinity.positiveInfinityOrder ℚ)).range
          (mumfordRaw M infinityHalf)) =
    Additive.ofMul
      (QuotientGroup.mk'
        (principalOriented M
          (N13Infinity.positiveInfinityOrder ℚ)).range
        (mumfordRaw M (infinityMinusMumford M)))
  rw [← map_mul, mumfordRaw_infinityHalf_sq, map_mul]
  have hprincipal :
      QuotientGroup.mk'
          (principalOriented M
            (N13Infinity.positiveInfinityOrder ℚ)).range
          (principalOriented M
            (N13Infinity.positiveInfinityOrder ℚ) halfFunctionUnit) =
        1 := by
    exact (QuotientGroup.eq_one_iff _).mpr
      (MonoidHom.mem_range.mpr ⟨halfFunctionUnit, rfl⟩)
  rw [hprincipal]
  exact congrArg
    (fun z :
      OrientedFrac M ⧸
        (principalOriented M
          (N13Infinity.positiveInfinityOrder ℚ)).range =>
      Additive.ofMul z)
    (one_mul
      (QuotientGroup.mk'
        (principalOriented M
          (N13Infinity.positiveInfinityOrder ℚ)).range
        (mumfordRaw M (infinityMinusMumford M))))

end

end MazurProof.N13InfinityHalf


