-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13NormalizedHermiteResidual_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13NormalizedHermiteResidual_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T02:55:02.391853+00:00
-- url     : https://prove2.me/theorems/74d34f69-7595-4b6e-afe8-dd616495b1a8
-- title:
--   FLT.Assumptions.MazurProof.N13NormalizedHermiteResidual source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13NormalizedHermiteResidual

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13NormalizedHermiteResidual
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13HermiteResidualDivisibility_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

The residual produced by integral Hermite interpolation has unit leading
coefficient 1-b1, not necessarily leading coefficient 1. Divide by this
actual unit to construct a monic quadratic residual over Z2, retaining the
unit scale in the exact norm equation.
-/

namespace MazurProof.N13NormalizedHermiteResidual

noncomputable section
open Polynomial N13CenteredHermiteFirstOrder N13HermiteResidualDivisibility
local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem coordIdeal_le_maximal (P : DiskPair) : I P ≤ N13TwoAdicDisks.maximal := by
  apply Ideal.span_le.mpr
  rintro a ⟨j, rfl⟩
  exact P.coord_mem_maximal j

theorem one_sub_unit (P : DiskPair) (b : R₂) (hb : b ∈ I P * I P) : IsUnit (1 - b) := by
  have hi : I P * I P ≤ I P := Ideal.mul_le_left
  have hm := coordIdeal_le_maximal P (hi hb)
  apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal isUnit_one
  convert N13TwoAdicDisks.maximal.neg_mem hm using 1 <;> ring

theorem residual_coeff_six (a₀ a₁ b₀ b₁ : R₂) :
    (N13HermiteResidualDivisibility.residual a₀ a₁ b₀ b₁).coeff 6 = 1 - b₁ := by
  -- Use a helper lemma to compute the coefficient
  have h : (N13HermiteResidualDivisibility.residual a₀ a₁ b₀ b₁) =
      Polynomial.C (1 - b₁) * Polynomial.X ^ 6 +
      Polynomial.C (-a₁*b₁ + 2*a₁ - b₀ - b₁^2 + 1) * Polynomial.X ^ 5 +
      Polynomial.C (-a₀*b₁ + 2*a₀ + a₁^2 - a₁*b₀ + 2*a₁ - 2*b₀*b₁ - b₁) * Polynomial.X ^ 4 +
      Polynomial.C (2*a₀*a₁ - a₀*b₀ + 2*a₀ + a₁^2 - a₁*b₁ - b₀^2 - b₀ - b₁) * Polynomial.X ^ 3 +
      Polynomial.C (a₀^2 + 2*a₀*a₁ - a₀*b₁ - a₁*b₀ - a₁*b₁ - b₀) * Polynomial.X ^ 2 +
      Polynomial.C (a₀^2 - a₀*b₀ - a₀*b₁ - a₁*b₀) * Polynomial.X +
      Polynomial.C (-a₀*b₀) := by
    unfold N13HermiteResidualDivisibility.residual N13HermiteResidualDivisibility.quad N13HermiteResidualDivisibility.lin
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_one, map_ofNat]
    ring
  rw [h]
  -- Now compute coeff 6 of the sum
  -- Only the first term contributes to coeff 6
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  -- Handle the remaining terms: constant polynomials have coeff n = 0 for n > 0
  -- Use coeff_eq_zero_of_natDegree_lt for constant polynomials
  simp [Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.natDegree_C,
    Polynomial.natDegree_pow, Polynomial.coeff_C_mul_X_pow]
  <;> norm_num
  <;> rfl

theorem residual_degree_le (a₀ a₁ b₀ b₁ : R₂) :
    (N13HermiteResidualDivisibility.residual a₀ a₁ b₀ b₁).natDegree ≤ 6 := by
  unfold N13HermiteResidualDivisibility.residual N13HermiteResidualDivisibility.quad N13HermiteResidualDivisibility.lin
  compute_degree!

theorem normalize_residual_factor
    (P : DiskPair) (a₀ a₁ b₀ b₁ : R₂) (q : R₂[X])
    (hb₁ : b₁ ∈ I P * I P)
    (hf : N13HermiteResidualDivisibility.residual a₀ a₁ b₀ b₁ = P.u ^ 2 * q) :
    ∃ Q : R₂[X], Q.Monic ∧ Q.natDegree = 2 ∧
      N13HermiteResidualDivisibility.residual a₀ a₁ b₀ b₁ = C (1 - b₁) * P.u ^ 2 * Q := by
  have hu := one_sub_unit P b₁ hb₁
  let v : R₂ˣ := hu.unit
  have hv : (v : R₂) = 1 - b₁ := hu.unit_spec
  have hc : (N13HermiteResidualDivisibility.residual a₀ a₁ b₀ b₁).coeff 6 ≠ 0 := by
    rw [residual_coeff_six]
    exact hu.ne_zero
  have hdeg : (N13HermiteResidualDivisibility.residual a₀ a₁ b₀ b₁).natDegree = 6 :=
    natDegree_eq_of_le_of_coeff_ne_zero (residual_degree_le _ _ _ _) hc
  have hq : q ≠ 0 := by
    intro h
    rw [h, mul_zero] at hf
    exact hc (by rw [hf]; simp)
  have hdq : q.natDegree = 2 := by
    rw [hf, natDegree_mul (pow_ne_zero 2 P.u_monic.ne_zero) hq,
      natDegree_pow, N13TwoAdicAbelChartPic.DiskPair.u_natDegree P] at hdeg
    omega
  have hl : q.leadingCoeff = 1 - b₁ := by
    have h := congrArg leadingCoeff hf
    rw [leadingCoeff, hdeg, residual_coeff_six,
      leadingCoeff_monic_mul (P.u_monic.pow 2)] at h
    exact h.symm
  refine ⟨C (↑(v⁻¹) : R₂) * q, ?_, ?_, ?_⟩
  · apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [hl, ← hv]
    exact Units.inv_mul v
  · rw [natDegree_C_mul_of_isUnit (v⁻¹).isUnit, hdq]
  · rw [hf]
    have hinv : C (1 - b₁) * C (↑(v⁻¹) : R₂) = (1 : R₂[X]) := by
      rw [← C_mul, ← hv, Units.mul_inv, C_1]
    calc
      P.u ^ 2 * q = 1 * (P.u ^ 2 * q) := by ring
      _ = (C (1 - b₁) * C (↑(v⁻¹) : R₂)) * (P.u ^ 2 * q) := by rw [hinv]
      _ = C (1 - b₁) * P.u ^ 2 * (C (↑(v⁻¹) : R₂) * q) := by ring

/-- Unconditional monic quadratic residual and its correctly scaled norm
factorization. Its Picard-class identification is not part of this theorem. -/
theorem exists_monic_residual (P : DiskPair) :
    ∃ a₀ a₁ b₀ b₁ : R₂, ∃ Q : R₂[X],
      Q.Monic ∧ Q.natDegree = 2 ∧ IsUnit (1 - b₁) ∧
      N13HermiteResidualDivisibility.residual a₀ a₁ b₀ b₁ = C (1 - b₁) * P.u ^ 2 * Q ∧
      b₀ ∈ I P * I P ∧ b₁ ∈ I P * I P ∧
      a₀ - 2 * P.x₀ * P.x₁ ∈ I P * I P ∧
      a₁ + 2 * (P.x₀ + P.x₁) + 1 ∈ I P * I P := by
  obtain ⟨a₀, a₁, b₀, b₁, q, hf, hb₀, hb₁, ha₀, ha₁⟩ := exists_residual_factor P
  obtain ⟨Q, hQ, hdQ, hn⟩ := normalize_residual_factor P _ _ _ _ q hb₁ hf
  exact ⟨a₀, a₁, b₀, b₁, Q, hQ, hdQ, one_sub_unit P b₁ hb₁,
    hn, hb₀, hb₁, ha₀, ha₁⟩

end
end MazurProof.N13NormalizedHermiteResidual


