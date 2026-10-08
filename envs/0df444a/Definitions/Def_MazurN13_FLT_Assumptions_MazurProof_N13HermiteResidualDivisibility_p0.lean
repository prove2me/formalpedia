-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13HermiteResidualDivisibility_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13HermiteResidualDivisibility_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T02:52:14.925113+00:00
-- url     : https://prove2.me/theorems/f4616dfc-a380-485b-9626-ad44d5a99a74
-- title:
--   FLT.Assumptions.MazurProof.N13HermiteResidualDivisibility source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13HermiteResidualDivisibility

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13HermiteResidualDivisibility
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralHermiteNumerator_p0
import Mathlib.RingTheory.Coprime.Lemmas

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

Use the actual implicit tangent slopes on the conjugate sheets. The
constructed numerator's norm has uBase as an explicit factor. Its residual
is divisible by u(P)^2 even when P shares an x-coordinate with the base
divisor: cancellation is by the unit conjugate ordinate, never by uBase(x).
-/

namespace MazurProof.N13HermiteResidualDivisibility

noncomputable section
open Polynomial N13CenteredHermiteFirstOrder
local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem opposite_curve (P : DiskPair) (j : Fin 2) :
    oppositeY P j ^ 2 + (x P j ^ 3 + x P j + 1) * oppositeY P j -
      (x P j ^ 2 + x P j) * x P j ^ 3 = 0 := by
  fin_cases j
  · have h := P.y₀_spec.1
    dsimp [N13GoodModelTwo.AffineEquation, N13GoodModelTwo.h, N13GoodModelTwo.rhs] at h
    dsimp [x, oppositeY, N13GoodModelTwo.h]
    linear_combination h
  · have h := P.y₁_spec.1
    dsimp [N13GoodModelTwo.AffineEquation, N13GoodModelTwo.h, N13GoodModelTwo.rhs] at h
    dsimp [x, oppositeY, N13GoodModelTwo.h]
    linear_combination h

theorem vertical_derivative_unit (P : DiskPair) (j : Fin 2) :
    IsUnit (2 * oppositeY P j + (x P j ^ 3 + x P j + 1)) := by
  have h₀ : IsUnit (2 * P.y₀ + N13GoodModelTwo.h P.x₀) := by
    apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal
      (N13TwoAdicDisks.h_isUnit_of_mem_zeroDisk P.x₀_mem)
    convert N13TwoAdicDisks.maximal.mul_mem_left 2 P.y₀_spec.2 using 1 <;> ring
  have h₁ : IsUnit (2 * P.y₁ + N13GoodModelTwo.h P.x₁) := by
    apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal
      (N13TwoAdicDisks.h_isUnit_of_mem_negOneDisk P.x₁_add_one_mem)
    convert N13TwoAdicDisks.maximal.mul_mem_left 2 P.y₁_spec.2 using 1 <;> ring
  fin_cases j
  · convert h₀.neg using 1 <;> dsimp [x, oppositeY, N13GoodModelTwo.h] <;> ring
  · convert h₁.neg using 1 <;> dsimp [x, oppositeY, N13GoodModelTwo.h] <;> ring

def slope (P : DiskPair) (j : Fin 2) : R₂ :=
  (5 * x P j ^ 4 + 4 * x P j ^ 3 -
    (3 * x P j ^ 2 + 1) * oppositeY P j) *
      (↑((vertical_derivative_unit P j).unit⁻¹) : R₂)

theorem slope_relation (P : DiskPair) (j : Fin 2) :
    (2 * oppositeY P j + (x P j ^ 3 + x P j + 1)) * slope P j +
      (3 * x P j ^ 2 + 1) * oppositeY P j -
        (5 * x P j ^ 4 + 4 * x P j ^ 3) = 0 := by
  have hi : (2 * oppositeY P j + (x P j ^ 3 + x P j + 1)) *
      (↑((vertical_derivative_unit P j).unit⁻¹) : R₂) = 1 := by
    exact (vertical_derivative_unit P j).mul_val_inv
  dsimp [slope]
  linear_combination
    (5 * x P j ^ 4 + 4 * x P j ^ 3 -
      (3 * x P j ^ 2 + 1) * oppositeY P j) * hi

def quad (a₀ a₁ : R₂) : R₂[X] := X ^ 2 + C a₁ * X + C a₀
def lin (b₀ b₁ : R₂) : R₂[X] := C b₀ + C b₁ * X
def residual (a₀ a₁ b₀ b₁ : R₂) : R₂[X] :=
  (X ^ 2 + X) * quad a₀ a₁ ^ 2 -
    quad a₀ a₁ * lin b₀ b₁ * (X ^ 3 + X + 1) -
      lin b₀ b₁ ^ 2 * X ^ 3

theorem norm_factor (a₀ a₁ b₀ b₁ : R₂) :
    ((X ^ 2 + X) * quad a₀ a₁) ^ 2 -
      ((X ^ 2 + X) * quad a₀ a₁) * lin b₀ b₁ *
        N13GeneralizedMumfordIntegral.hPoly -
      lin b₀ b₁ ^ 2 * N13GeneralizedMumfordIntegral.rhsPoly =
        (X ^ 2 + X) * residual a₀ a₁ b₀ b₁ := by
  simp only [residual, N13GeneralizedMumfordIntegral.hPoly,
    N13GeneralizedMumfordIntegral.rhsPoly]
  ring

private theorem double_root_dvd (p : R₂[X]) (a : R₂)
    (h : p.eval a = 0) (hd : p.derivative.eval a = 0) : (X - C a) ^ 2 ∣ p := by
  obtain ⟨q, hq⟩ := (dvd_iff_isRoot.mpr h : X - C a ∣ p)
  rw [hq, derivative_mul] at hd
  have hq0 : q.eval a = 0 := by simpa using hd
  obtain ⟨r, hr⟩ := (dvd_iff_isRoot.mpr hq0 : X - C a ∣ q)
  refine ⟨r, ?_⟩
  rw [hq, hr, pow_two, mul_assoc]

theorem residual_double_root
    (P : DiskPair) (a₀ a₁ b₀ b₁ : R₂) (j : Fin 2)
    (hv : (x P j ^ 2 + x P j) * (x P j ^ 2 + a₁ * x P j + a₀) +
      (b₀ + b₁ * x P j) * oppositeY P j = 0)
    (hd : (2 * x P j + 1) * (x P j ^ 2 + a₁ * x P j + a₀) +
      (x P j ^ 2 + x P j) * (2 * x P j + a₁) +
      b₁ * oppositeY P j + (b₀ + b₁ * x P j) * slope P j = 0) :
    (X - C (x P j)) ^ 2 ∣ residual a₀ a₁ b₀ b₁ := by
  let A := x P j ^ 2 + a₁ * x P j + a₀
  let b := b₀ + b₁ * x P j
  let y := oppositeY P j
  have hc := opposite_curve P j
  have hcd := slope_relation P j
  have hzero : (residual a₀ a₁ b₀ b₁).eval (x P j) = 0 := by
    apply (mul_eq_zero.mp (show (residual a₀ a₁ b₀ b₁).eval (x P j) * y = 0 from ?_)).resolve_right
      (oppositeY_unit P j).ne_zero
    simp only [residual, quad, lin, eval_sub, eval_mul, eval_pow, eval_add, eval_X, eval_C, eval_one]
    dsimp [A, b, y]
    linear_combination
      ((x P j ^ 2 + a₁ * x P j + a₀) * oppositeY P j -
        (b₀ + b₁ * x P j) * x P j ^ 3) * hv -
      (x P j ^ 2 + a₁ * x P j + a₀) * (b₀ + b₁ * x P j) * hc
  apply double_root_dvd _ _ hzero
  apply (mul_eq_zero.mp (show (residual a₀ a₁ b₀ b₁).derivative.eval (x P j) * y = 0 from ?_)).resolve_right
    (oppositeY_unit P j).ne_zero
  have hz := hzero
  simp only [residual, quad, lin, eval_sub, eval_mul, eval_pow, eval_add, eval_X, eval_C, eval_one] at hz
  simp [residual, quad, lin, derivative_mul, derivative_pow, y, -mul_eq_zero]
  linear_combination
    ((x P j ^ 2 + a₁ * x P j + a₀) * oppositeY P j -
      (b₀ + b₁ * x P j) * x P j ^ 3) * hd +
    ((2 * x P j + a₁) * oppositeY P j +
      (x P j ^ 2 + a₁ * x P j + a₀) * slope P j - b₁ * x P j ^ 3 -
        3 * (b₀ + b₁ * x P j) * x P j ^ 2) * hv -
    slope P j * hz -
    ((2 * x P j + a₁) * (b₀ + b₁ * x P j) +
      (x P j ^ 2 + a₁ * x P j + a₀) * b₁) * hc -
    (x P j ^ 2 + a₁ * x P j + a₀) * (b₀ + b₁ * x P j) * hcd

/-- A genuine exact residual factor, constructed for each actual disk pair.
This retains the norm identity before any residual-divisor identification. -/
theorem exists_residual_factor (P : DiskPair) :
    ∃ a₀ a₁ b₀ b₁ : R₂, ∃ q : R₂[X],
      residual a₀ a₁ b₀ b₁ = P.u ^ 2 * q ∧
      b₀ ∈ I P * I P ∧ b₁ ∈ I P * I P ∧
      a₀ - 2 * P.x₀ * P.x₁ ∈ I P * I P ∧
      a₁ + 2 * (P.x₀ + P.x₁) + 1 ∈ I P * I P := by
  obtain ⟨a₀, a₁, b₀, b₁, hv, hd, hm⟩ :=
    N13IntegralHermiteNumerator.exists_normalized_coefficients P (slope P)
  have h₀ := residual_double_root P a₀ a₁ b₀ b₁ 0 (hv 0) (hd 0)
  have h₁ := residual_double_root P a₀ a₁ b₀ b₁ 1 (hv 1) (hd 1)
  have hc : IsCoprime ((X - C P.x₁) ^ 2) ((X - C P.x₀) ^ 2) :=
    (isCoprime_X_sub_C_of_isUnit_sub P.x₁_sub_x₀_isUnit).pow
  have hdiv : P.u ^ 2 ∣ residual a₀ a₁ b₀ b₁ := by
    simpa [N13TwoAdicAbelChartData.DiskPair.u, mul_pow, mul_comm, x] using hc.mul_dvd h₁ h₀
  obtain ⟨q, hq⟩ := hdiv
  exact ⟨a₀, a₁, b₀, b₁, q, hq, hm⟩

end
end MazurProof.N13HermiteResidualDivisibility


