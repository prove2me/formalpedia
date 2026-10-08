-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordCenteredDoublingJet_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13MumfordCenteredDoublingJet_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T00:35:35.637844+00:00
-- url     : https://prove2.me/theorems/1db25504-816b-4b90-ae4c-c0038e482cbf
-- title:
--   FLT.Assumptions.MazurProof.N13MumfordCenteredDoublingJet source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13MumfordCenteredDoublingJet

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13MumfordCenteredDoublingJet
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordFormalTransitionJet_p0

set_option autoImplicit false




/-!
# Denominator-free centered doubling jets for N13

Let `u_B = X² + X` be the fixed Abel-chart base polynomial and let `u_P`
be the monic quadratic of a disk pair.  The square of the centered transition
`u_P / u_B` has a canonical first-order monic normalization

`u_square = 2 * u_P - u_B`.

Cross-multiplication gives the exact error

`u_P² - u_B * u_square = (u_P - u_B)²`.

Thus its constant and linear deviations are the doubled disk coordinates
modulo the square of the moving coordinate ideal.  These identities are the
denominator-free polynomial core of the missing first-jet doubling theorem;
identifying the chosen representative of the doubled Picard class with this
normalization remains a separate step.
-/

open Polynomial

namespace MazurProof.N13MumfordCenteredDoublingJet

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The two-adic coefficient domain of the integral N13 model. -/
abbrev R₂ : Type := ℤ_[2]

/-- A pair of Hensel-selected points in the two distinguished Abel disks. -/
abbrev DiskPair : Type :=
  N13TwoAdicAbelChartData.DiskPair

/-- The monic quadratic obtained by squaring the centered `u`-transition and
cancelling one copy of the fixed base polynomial to first order. -/
def centeredSquareU (P : DiskPair) : R₂[X] :=
  P.u + P.u - N13AbelChartBase.baseSmoothMumford.u

/-- Cross-multiplication removes every overlap denominator: the error between
the unreduced numerator `u_P²` and its centered monic normalization is exactly
the square of the deviation from the base polynomial. -/
theorem u_sq_sub_base_mul_centeredSquareU
    (P : DiskPair) :
    P.u ^ 2 -
        N13AbelChartBase.baseSmoothMumford.u *
          centeredSquareU P =
      (P.u - N13AbelChartBase.baseSmoothMumford.u) ^ 2 := by
  simp only [centeredSquareU]
  ring

/-- The constant coefficient of the normalized centered square differs from
`-2*x₀` by exactly twice the mixed quadratic disk coordinate. -/
theorem centeredSquareU_coeff_zero_exact
    (P : DiskPair) :
    (centeredSquareU P -
          N13AbelChartBase.baseSmoothMumford.u).coeff 0 +
        (P.x₀ + P.x₀) =
      P.x₀ * (P.x₁ + 1) +
        P.x₀ * (P.x₁ + 1) := by
  have hdev :
      centeredSquareU P -
          N13AbelChartBase.baseSmoothMumford.u =
        (P.u - N13AbelChartBase.baseSmoothMumford.u) +
          (P.u - N13AbelChartBase.baseSmoothMumford.u) := by
    simp only [centeredSquareU]
    ring
  rw [hdev, N13MumfordFormalTransitionJet.u_sub_base]
  simp
  ring

/-- The linear coefficient of the normalized centered square is exactly
`-2*(x₀+x₁+1)`. -/
theorem centeredSquareU_coeff_one_exact
    (P : DiskPair) :
    (centeredSquareU P -
          N13AbelChartBase.baseSmoothMumford.u).coeff 1 +
        ((P.x₀ + (P.x₁ + 1)) +
          (P.x₀ + (P.x₁ + 1))) = 0 := by
  have hdev :
      centeredSquareU P -
          N13AbelChartBase.baseSmoothMumford.u =
        (P.u - N13AbelChartBase.baseSmoothMumford.u) +
          (P.u - N13AbelChartBase.baseSmoothMumford.u) := by
    simp only [centeredSquareU]
    ring
  rw [hdev, N13MumfordFormalTransitionJet.u_sub_base]
  simp
  ring

/-- The constant coefficient of the centered square has only a mixed
quadratic error, hence lies in the square of the moving coordinate ideal. -/
theorem centeredSquareU_coeff_zero_mod_sq
    (P : DiskPair) :
    (centeredSquareU P -
          N13AbelChartBase.baseSmoothMumford.u).coeff 0 +
        (P.x₀ + P.x₀) ∈
      N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P *
        N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P := by
  let I :=
    N13TwoAdicKernelChart.coordIdeal
      N13TwoAdicAbelChartData.DiskPair.coord P
  have hr : P.x₀ ∈ I := by
    apply Ideal.subset_span
    exact Set.mem_range_self (0 : Fin 2)
  have hs : P.x₁ + 1 ∈ I := by
    apply Ideal.subset_span
    exact Set.mem_range_self (1 : Fin 2)
  have hrs : P.x₀ * (P.x₁ + 1) ∈ I * I :=
    Ideal.mul_mem_mul hr hs
  rw [centeredSquareU_coeff_zero_exact]
  exact (I * I).add_mem hrs hrs

/-- The linear coefficient has zero quadratic error, so it belongs to the
square of the moving coordinate ideal without any further estimate. -/
theorem centeredSquareU_coeff_one_mod_sq
    (P : DiskPair) :
    (centeredSquareU P -
          N13AbelChartBase.baseSmoothMumford.u).coeff 1 +
        ((P.x₀ + (P.x₁ + 1)) +
          (P.x₀ + (P.x₁ + 1))) ∈
      N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P *
        N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P := by
  rw [centeredSquareU_coeff_one_exact]
  exact Ideal.zero_mem _

/-! ## A curve-compatible linearized double -/

/-- The monic quadratic carrying twice the first-order disk displacement
from the fixed Abel-chart base. -/
def doubledLinearU (P : DiskPair) : R₂[X] :=
  N13FormalAbelLinearization.uBase +
    C (-(P.x₀ + P.x₀)) +
    C (-((P.x₀ + (P.x₁ + 1)) +
      (P.x₀ + (P.x₁ + 1)))) * X

/-- The graph ordinate carrying twice the first-order slope on the
negative-one disk. -/
def doubledLinearV (P : DiskPair) : R₂[X] :=
  C ((P.x₁ + 1) + (P.x₁ + 1)) * X

/-- The quotient polynomial forced by the linearized generalized Mumford
equation for the doubled displacement. -/
def doubledLinearW (P : DiskPair) : R₂[X] :=
  -X ^ 3 + C (-(P.x₀ + P.x₀)) * X ^ 2 +
    C ((P.x₁ + 1) + (P.x₁ + 1))

/-- The linear part of the integral N13 curve equation is satisfied exactly
by the doubled local Mumford displacement. -/
theorem doubledLinear_first_order_identity
    (P : DiskPair) :
    N13GeneralizedMumfordIntegral.hPoly * doubledLinearV P =
      N13FormalAbelLinearization.uBase *
          (doubledLinearW P + X ^ 3) +
        (doubledLinearU P -
          N13FormalAbelLinearization.uBase) * (-X ^ 3) := by
  simp [doubledLinearU, doubledLinearV, doubledLinearW,
    N13FormalAbelLinearization.uBase,
    N13GeneralizedMumfordIntegral.hPoly]
  ring

/-- The entire failure of the doubled linear triple to satisfy the integral
curve equation is the sum of products of first-order coordinate
polynomials, and is therefore quadratic in the moving disk coordinates. -/
theorem doubledLinear_curve_error
    (P : DiskPair) :
    doubledLinearV P ^ 2 +
          N13GeneralizedMumfordIntegral.hPoly * doubledLinearV P -
        N13GeneralizedMumfordIntegral.rhsPoly -
          doubledLinearU P * doubledLinearW P =
      doubledLinearV P ^ 2 -
        (doubledLinearU P -
          N13FormalAbelLinearization.uBase) *
        (doubledLinearW P + X ^ 3) := by
  simp [doubledLinearU, doubledLinearV, doubledLinearW,
    N13FormalAbelLinearization.uBase,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GeneralizedMumfordIntegral.rhsPoly]
  ring

/-- The transition-normalized centered square and the curve-compatible
linear quadratic differ by exactly twice the mixed quadratic coordinate. -/
theorem centeredSquareU_sub_doubledLinearU
    (P : DiskPair) :
    centeredSquareU P - doubledLinearU P =
      C (P.x₀ * (P.x₁ + 1) +
        P.x₀ * (P.x₁ + 1)) := by
  simp [centeredSquareU, doubledLinearU,
    N13TwoAdicAbelChartData.DiskPair.u,
    N13FormalAbelLinearization.uBase]
  ring

/-! ## Quadratic Hensel expansions of the selected ordinates -/

/-- At the zero base point, substituting the base graph `y=0` leaves the
explicit fourth-order residual `-x⁴(x+1)`. -/
theorem affineResidual_zero_reference (x : R₂) :
    N13GoodModelTwo.affineResidual x 0 =
      -(x ^ 4 * (x + 1)) := by
  simp [N13GoodModelTwo.affineResidual,
    N13GoodModelTwo.h, N13GoodModelTwo.rhs]
  ring

/-- At the negative-one base point, the first-order graph `y=-(x+1)`
leaves exactly the quadratic residual `-x³(x+1)²`. -/
theorem affineResidual_negOne_reference (x : R₂) :
    N13GoodModelTwo.affineResidual x (-(x + 1)) =
      -(x ^ 3 * (x + 1) ^ 2) := by
  simp [N13GoodModelTwo.affineResidual,
    N13GoodModelTwo.h, N13GoodModelTwo.rhs]
  ring

/-- Cancellation by a unit preserves membership in an ideal. -/
private theorem mem_of_mul_mem_right_isUnit
    (J : Ideal R₂) {a b : R₂}
    (hb : IsUnit b) (hab : a * b ∈ J) : a ∈ J := by
  obtain ⟨u, rfl⟩ := hb
  have h := J.mul_mem_left (↑u⁻¹) hab
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

/-- The Hensel-selected ordinate above the zero disk has no linear term in
the two disk coordinates. -/
theorem y₀_mem_coordIdeal_sq (P : DiskPair) :
    P.y₀ ∈
      N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P *
        N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P := by
  let I :=
    N13TwoAdicKernelChart.coordIdeal
      N13TwoAdicAbelChartData.DiskPair.coord P
  have hr : P.x₀ ∈ I := by
    apply Ideal.subset_span
    exact Set.mem_range_self (0 : Fin 2)
  have hunit :
      IsUnit (P.y₀ + N13GoodModelTwo.h P.x₀) := by
    apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal
      (N13TwoAdicDisks.h_isUnit_of_mem_zeroDisk P.x₀_mem)
    convert P.y₀_spec.2 using 1
    ring
  have hprod :
      P.y₀ * (P.y₀ + N13GoodModelTwo.h P.x₀) =
        N13GoodModelTwo.rhs P.x₀ := by
    calc
      P.y₀ * (P.y₀ + N13GoodModelTwo.h P.x₀) =
          P.y₀ ^ 2 + N13GoodModelTwo.h P.x₀ * P.y₀ := by
            ring
      _ = N13GoodModelTwo.rhs P.x₀ := P.y₀_spec.1
  have hrr : P.x₀ * P.x₀ ∈ I * I :=
    Ideal.mul_mem_mul hr hr
  have hrhs : N13GoodModelTwo.rhs P.x₀ ∈ I * I := by
    have h :=
      (I * I).mul_mem_right
        (P.x₀ ^ 2 * (P.x₀ + 1)) hrr
    convert h using 1
    simp [N13GoodModelTwo.rhs]
    ring
  rw [← hprod] at hrhs
  exact mem_of_mul_mem_right_isUnit (I * I) hunit hrhs

/-- The Hensel-selected ordinate above the negative-one disk has linear term
`-(x₁+1)` and only quadratic remaining error. -/
theorem y₁_add_coord_mem_sq (P : DiskPair) :
    P.y₁ + (P.x₁ + 1) ∈
      N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P *
        N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P := by
  let I :=
    N13TwoAdicKernelChart.coordIdeal
      N13TwoAdicAbelChartData.DiskPair.coord P
  let s : R₂ := P.x₁ + 1
  have hs : s ∈ I := by
    apply Ideal.subset_span
    exact Set.mem_range_self (1 : Fin 2)
  have hdelta : P.y₁ - s ∈ N13TwoAdicDisks.maximal :=
    N13TwoAdicDisks.maximal.sub_mem P.y₁_spec.2
      P.x₁_add_one_mem
  have hunit :
      IsUnit (P.y₁ - s + N13GoodModelTwo.h P.x₁) := by
    apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal
      (N13TwoAdicDisks.h_isUnit_of_mem_negOneDisk
        P.x₁_add_one_mem)
    convert hdelta using 1
    ring
  have hprod :
      (P.y₁ + s) *
          (P.y₁ - s + N13GoodModelTwo.h P.x₁) =
        P.x₁ ^ 3 * s ^ 2 := by
    calc
      (P.y₁ + s) *
          (P.y₁ - s + N13GoodModelTwo.h P.x₁) =
        N13GoodModelTwo.affineResidual P.x₁ P.y₁ -
          N13GoodModelTwo.affineResidual P.x₁ (-s) := by
            simp [N13GoodModelTwo.affineResidual]
            ring
      _ = P.x₁ ^ 3 * s ^ 2 := by
        have hcurve :
            N13GoodModelTwo.affineResidual P.x₁ P.y₁ = 0 :=
          (N13GoodModelTwo.affineEquation_iff_residual
            P.x₁ P.y₁).mp P.y₁_spec.1
        rw [hcurve, affineResidual_negOne_reference]
        simp [s]
  have hss : s * s ∈ I * I :=
    Ideal.mul_mem_mul hs hs
  have hrhs : P.x₁ ^ 3 * s ^ 2 ∈ I * I := by
    have h := (I * I).mul_mem_left (P.x₁ ^ 3) hss
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h
  rw [← hprod] at hrhs
  exact mem_of_mul_mem_right_isUnit (I * I) hunit hrhs

/-! ## Reduction from cross-multiplied normalization to coordinate doubling -/

/-- Membership of only coefficients one and three in the cross-multiplied
centered product implies the two coefficient congruences for the monic
polynomial of a proposed double.

The calculation is stated for an arbitrary ideal containing the two
coordinates of `P`.  The constant coefficient has one additional product of
the two first-order coefficients of `u_P-u_B`; the linear coefficient is
exactly the negative of cross coefficient three. -/
theorem centeredUDeviation_double_mod_ideal_sq_of_cross
    (J : Ideal R₂) (P Q : DiskPair)
    (hr : P.x₀ ∈ J)
    (hs : P.x₁ + 1 ∈ J)
    (h₁ :
      (P.u ^ 2 -
        N13AbelChartBase.baseSmoothMumford.u * Q.u).coeff 1 ∈
        J * J)
    (h₃ :
      (P.u ^ 2 -
        N13AbelChartBase.baseSmoothMumford.u * Q.u).coeff 3 ∈
        J * J) :
    ((Q.u - N13AbelChartBase.baseSmoothMumford.u).coeff 0 -
          ((P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 0 +
            (P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 0) ∈
        J * J) ∧
      ((Q.u - N13AbelChartBase.baseSmoothMumford.u).coeff 1 -
          ((P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 1 +
            (P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 1) ∈
        J * J) := by
  let U := N13AbelChartBase.baseSmoothMumford.u
  let A := P.u - U
  let B := Q.u - U
  let E := P.u ^ 2 - U * Q.u
  let a₁ := -(P.x₀ + (P.x₁ + 1))
  let a₀ := P.x₀ * P.x₁
  let b₁ := -(Q.x₀ + (Q.x₁ + 1))
  let b₀ := Q.x₀ * Q.x₁
  let d₁ := a₁ + a₁ - b₁
  let d₀ := a₀ + a₀ - b₀
  have hU : U = X ^ 2 + X := by
    simp [U, N13FormalAbelLinearization.uBase]
  have hApoly : A = C a₁ * X + C a₀ := by
    simpa [A, U, a₁, a₀] using
      N13MumfordFormalTransitionJet.u_sub_base P
  have hBpoly : B = C b₁ * X + C b₀ := by
    simpa [B, U, b₁, b₀] using
      N13MumfordFormalTransitionJet.u_sub_base Q
  have hPu : P.u = U + (C a₁ * X + C a₀) := by
    calc
      P.u = U + A := by simp [A]
      _ = U + (C a₁ * X + C a₀) := by rw [hApoly]
  have hQu : Q.u = U + (C b₁ * X + C b₀) := by
    calc
      Q.u = U + B := by simp [B]
      _ = U + (C b₁ * X + C b₀) := by rw [hBpoly]
  have hEpoly :
      E =
        C d₁ * X ^ 3 +
          C (d₀ + d₁ + a₁ ^ 2) * X ^ 2 +
          C (d₀ + a₁ * a₀ + a₁ * a₀) * X +
          C (a₀ ^ 2) := by
    dsimp only [E]
    rw [hPu, hQu, hU]
    simp only [d₁, d₀, map_add, map_sub, map_mul, map_pow]
    ring
  have hA₀eq : A.coeff 0 = a₀ := by
    rw [hApoly]
    simp
  have hA₁eq : A.coeff 1 = a₁ := by
    rw [hApoly]
    simp
  have hB₀eq : B.coeff 0 = b₀ := by
    rw [hBpoly]
    simp
  have hB₁eq : B.coeff 1 = b₁ := by
    rw [hBpoly]
    simp
  have hE₁eq : E.coeff 1 = d₀ + a₁ * a₀ + a₁ * a₀ := by
    rw [hEpoly]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C]
    norm_num
  have hE₃eq : E.coeff 3 = d₁ := by
    rw [hEpoly]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C]
    norm_num
  have hA₀ : A.coeff 0 ∈ J := by
    rw [hA₀eq]
    dsimp only [a₀]
    exact J.mul_mem_right P.x₁ hr
  have hA₁ : A.coeff 1 ∈ J := by
    rw [hA₁eq]
    dsimp only [a₁]
    exact J.neg_mem (J.add_mem hr hs)
  have hzero :
      (Q.u - N13AbelChartBase.baseSmoothMumford.u).coeff 0 -
          ((P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 0 +
            (P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 0) =
        -(P.u ^ 2 -
            N13AbelChartBase.baseSmoothMumford.u * Q.u).coeff 1 +
          (P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 1 *
            (P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 0 +
          (P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 1 *
            (P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 0 := by
    change
      B.coeff 0 - (A.coeff 0 + A.coeff 0) =
        -(E.coeff 1) + A.coeff 1 * A.coeff 0 +
          A.coeff 1 * A.coeff 0
    rw [hA₀eq, hA₁eq, hB₀eq, hE₁eq]
    simp only [d₀]
    ring
  have hone :
      (Q.u - N13AbelChartBase.baseSmoothMumford.u).coeff 1 -
          ((P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 1 +
            (P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 1) =
        -(P.u ^ 2 -
            N13AbelChartBase.baseSmoothMumford.u * Q.u).coeff 3 := by
    change B.coeff 1 - (A.coeff 1 + A.coeff 1) = -(E.coeff 3)
    rw [hA₁eq, hB₁eq, hE₃eq]
    simp only [d₁]
    ring
  constructor
  · rw [hzero]
    exact
      (J * J).add_mem
        ((J * J).add_mem ((J * J).neg_mem h₁)
          (Ideal.mul_mem_mul hA₁ hA₀))
        (Ideal.mul_mem_mul hA₁ hA₀)
  · rw [hone]
    exact (J * J).neg_mem h₃

/-- Specializing the coefficient reducer to the moving coordinate ideal of
`P` gives the one-sided congruence used by the unary doubling chart. -/
theorem centeredUDeviation_double_mod_sq_of_cross
    (P Q : DiskPair)
    (h₁ :
      (P.u ^ 2 -
        N13AbelChartBase.baseSmoothMumford.u * Q.u).coeff 1 ∈
        N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P *
          N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P)
    (h₃ :
      (P.u ^ 2 -
        N13AbelChartBase.baseSmoothMumford.u * Q.u).coeff 3 ∈
        N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P *
          N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P) :
    ((Q.u - N13AbelChartBase.baseSmoothMumford.u).coeff 0 -
          ((P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 0 +
            (P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 0) ∈
        N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P *
          N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P) ∧
      ((Q.u - N13AbelChartBase.baseSmoothMumford.u).coeff 1 -
          ((P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 1 +
            (P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 1) ∈
        N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P *
          N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P) := by
  let I :=
    N13TwoAdicKernelChart.coordIdeal
      N13TwoAdicAbelChartData.DiskPair.coord P
  apply centeredUDeviation_double_mod_ideal_sq_of_cross I P Q
  · apply Ideal.subset_span
    exact Set.mem_range_self (0 : Fin 2)
  · apply Ideal.subset_span
    exact Set.mem_range_self (1 : Fin 2)
  · exact h₁
  · exact h₃

/-- The two odd cross coefficients determine the actual doubled disk
coordinates modulo the square of the original moving coordinate ideal.

The constant and linear coefficients first put both coordinates of `Q` in
the ideal of `P`; cancellation of the unit `Q.x₁` is the only local-ring
step.  The remaining difference between polynomial and disk coordinates is
a product of two first-order coordinates, hence quadratic. -/
theorem diskCoord_double_mod_sq_of_cross
    (P Q : DiskPair)
    (h₁ :
      (P.u ^ 2 -
        N13AbelChartBase.baseSmoothMumford.u * Q.u).coeff 1 ∈
        N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P *
          N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P)
    (h₃ :
      (P.u ^ 2 -
        N13AbelChartBase.baseSmoothMumford.u * Q.u).coeff 3 ∈
        N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P *
          N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P)
    (i : Fin 2) :
    N13TwoAdicAbelChartData.DiskPair.coord Q i -
          (N13TwoAdicAbelChartData.DiskPair.coord P i +
            N13TwoAdicAbelChartData.DiskPair.coord P i) ∈
        N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P *
          N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P := by
  let I :=
    N13TwoAdicKernelChart.coordIdeal
      N13TwoAdicAbelChartData.DiskPair.coord P
  let A := P.u - N13AbelChartBase.baseSmoothMumford.u
  let B := Q.u - N13AbelChartBase.baseSmoothMumford.u
  have hcoeff := centeredUDeviation_double_mod_sq_of_cross P Q h₁ h₃
  have hA₀ : A.coeff 0 = P.x₀ * P.x₁ := by
    rw [show A = P.u - N13AbelChartBase.baseSmoothMumford.u from rfl,
      N13MumfordFormalTransitionJet.u_sub_base]
    simp
  have hA₁ : A.coeff 1 = -(P.x₀ + (P.x₁ + 1)) := by
    rw [show A = P.u - N13AbelChartBase.baseSmoothMumford.u from rfl,
      N13MumfordFormalTransitionJet.u_sub_base]
    simp
  have hB₀ : B.coeff 0 = Q.x₀ * Q.x₁ := by
    rw [show B = Q.u - N13AbelChartBase.baseSmoothMumford.u from rfl,
      N13MumfordFormalTransitionJet.u_sub_base]
    simp
  have hB₁ : B.coeff 1 = -(Q.x₀ + (Q.x₁ + 1)) := by
    rw [show B = Q.u - N13AbelChartBase.baseSmoothMumford.u from rfl,
      N13MumfordFormalTransitionJet.u_sub_base]
    simp
  have hcoeff₀ :
      B.coeff 0 - (A.coeff 0 + A.coeff 0) ∈ I * I := by
    simpa only [A, B, I] using hcoeff.1
  have hcoeff₁ :
      B.coeff 1 - (A.coeff 1 + A.coeff 1) ∈ I * I := by
    simpa only [A, B, I] using hcoeff.2
  have hp₀ : P.x₀ ∈ I := by
    apply Ideal.subset_span
    exact Set.mem_range_self (0 : Fin 2)
  have hp₁ : P.x₁ + 1 ∈ I := by
    apply Ideal.subset_span
    exact Set.mem_range_self (1 : Fin 2)
  have hA₀mem : A.coeff 0 ∈ I := by
    rw [hA₀]
    exact I.mul_mem_right P.x₁ hp₀
  have hA₁mem : A.coeff 1 ∈ I := by
    rw [hA₁]
    exact I.neg_mem (I.add_mem hp₀ hp₁)
  have hB₀mem : B.coeff 0 ∈ I := by
    have hdiff : B.coeff 0 - (A.coeff 0 + A.coeff 0) ∈ I :=
      Ideal.mul_le_left hcoeff₀
    have hsum := I.add_mem hdiff (I.add_mem hA₀mem hA₀mem)
    convert hsum using 1
    ring
  have hB₁mem : B.coeff 1 ∈ I := by
    have hdiff : B.coeff 1 - (A.coeff 1 + A.coeff 1) ∈ I :=
      Ideal.mul_le_left hcoeff₁
    have hsum := I.add_mem hdiff (I.add_mem hA₁mem hA₁mem)
    convert hsum using 1
    ring
  have hx₁unit : IsUnit Q.x₁ := by
    apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal isUnit_neg_one
    simpa using Q.x₁_add_one_mem
  have hq₀ : Q.x₀ ∈ I := by
    rw [hB₀] at hB₀mem
    exact mem_of_mul_mem_right_isUnit I hx₁unit hB₀mem
  have hq₁ : Q.x₁ + 1 ∈ I := by
    rw [hB₁] at hB₁mem
    have hsumRaw := I.neg_mem hB₁mem
    have hsum : Q.x₀ + (Q.x₁ + 1) ∈ I := by
      convert hsumRaw using 1
      ring
    have hsub := I.sub_mem hsum hq₀
    convert hsub using 1
    ring
  have hpProd : P.x₀ * (P.x₁ + 1) ∈ I * I :=
    Ideal.mul_mem_mul hp₀ hp₁
  have hqProd : Q.x₀ * (Q.x₁ + 1) ∈ I * I :=
    Ideal.mul_mem_mul hq₀ hq₁
  have hcoord₀ :
      Q.x₀ - (P.x₀ + P.x₀) ∈ I * I := by
    have hprodDiff :
        Q.x₀ * (Q.x₁ + 1) -
            (P.x₀ * (P.x₁ + 1) +
              P.x₀ * (P.x₁ + 1)) ∈ I * I :=
      (I * I).sub_mem hqProd ((I * I).add_mem hpProd hpProd)
    have hsum := (I * I).add_mem ((I * I).neg_mem hcoeff₀) hprodDiff
    rw [hA₀, hB₀] at hsum
    convert hsum using 1
    ring
  have hcoord₁ :
      (Q.x₁ + 1) -
          ((P.x₁ + 1) + (P.x₁ + 1)) ∈ I * I := by
    have hsum := (I * I).sub_mem ((I * I).neg_mem hcoeff₁) hcoord₀
    rw [hA₁, hB₁] at hsum
    convert hsum using 1
    ring
  fin_cases i
  · change
      Q.x₀ - (P.x₀ + P.x₀) ∈
        N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P *
          N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P
    simpa only [I] using hcoord₀
  · change
      (Q.x₁ + 1) - ((P.x₁ + 1) + (P.x₁ + 1)) ∈
        N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P *
          N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P
    simpa only [I] using hcoord₁

end

end MazurProof.N13MumfordCenteredDoublingJet


