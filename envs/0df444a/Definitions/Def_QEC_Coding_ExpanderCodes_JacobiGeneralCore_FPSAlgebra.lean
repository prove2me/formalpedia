-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
-- name    : QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:52:02.994683+00:00
-- url     : https://prove2.me/theorems/04637987-30f4-41cc-bb70-772b9977ff26
-- title:
--   FPSAlgebra
-- statement:
--   Definitions and structural lemmas for FPSAlgebra, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSAlgebra.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_constantCoeff_qPochhammer_X
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_isUnit_qPochhammerInf
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_succ_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_right
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_succ_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_right
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_succ
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qPochhammer_zero


set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
def qPochhammerInv (k : ℕ) : R⟦X⟧ :=
  MvPowerSeries.invOfUnit (qPochhammer (X : R⟦X⟧) k) 1
omit [TopologicalSpace R] [DiscreteTopology R] in
/-- `qPochhammer X k` times its formal power series inverse equals 1. -/
@[simp]
theorem qPochhammer_X_mul_qPochhammerInv (k : ℕ) :
    qPochhammer (X : R⟦X⟧) k * qPochhammerInv (R := R) k = 1 :=
  PowerSeries.mul_invOfUnit _ 1 (by simpa using constantCoeff_qPochhammer_X (R := R) k)
omit [TopologicalSpace R] [DiscreteTopology R] in
/-- The formal power series inverse of `qPochhammer X k` times `qPochhammer X k` equals 1. -/
@[simp]
theorem qPochhammerInv_mul_qPochhammer_X (k : ℕ) :
    qPochhammerInv (R := R) k * qPochhammer (X : R⟦X⟧) k = 1 := by
  rw [mul_comm, qPochhammer_X_mul_qPochhammerInv]
theorem isUnit_qPochhammerInf_X : IsUnit (qPochhammerInf (X : R⟦X⟧)) :=
  isUnit_qPochhammerInf X (by simp)
def qPochhammerInfInv : R⟦X⟧ := ↑(isUnit_qPochhammerInf_X (R := R)).unit⁻¹
@[simp]
theorem qPochhammerInf_X_mul_qPochhammerInfInv :
    qPochhammerInf (X : R⟦X⟧) * qPochhammerInfInv (R := R) = 1 :=
  isUnit_qPochhammerInf_X.mul_val_inv
@[simp]
theorem qPochhammerInfInv_mul_qPochhammerInf_X :
    qPochhammerInfInv (R := R) * qPochhammerInf (X : R⟦X⟧) = 1 :=
  isUnit_qPochhammerInf_X.val_inv_mul
section Euler2
end Euler2
section KeyIdentity
def keySum (k : ℕ) : R⟦X⟧ :=
  ∑' m : ℕ, X ^ (m * (m + k)) * qPochhammerInv (R := R) m * qPochhammerInv (m + k)
def keySumShift (k : ℕ) : R⟦X⟧ :=
  ∑' m : ℕ, X ^ (m * (m + k)) * qPochhammerInv (R := R) m * qPochhammerInv (m + k + 1)
end KeyIdentity
section Cauchy
end Cauchy
section JTP
def diagonalEquiv : ℕ × ℕ ≃ (ℕ × ℕ) ⊕ (ℕ × ℕ) where
  toFun p := if p.2 ≤ p.1 then Sum.inl (p.1 - p.2, p.2) else Sum.inr (p.2 - p.1 - 1, p.1)
  invFun s := match s with
    | Sum.inl (k, m) => (m + k, m)
    | Sum.inr (l, n) => (n, n + l + 1)
  left_inv := by intro ⟨n, m⟩; simp only; split_ifs with h <;> simp <;> omega
  right_inv := by
    intro s
    rcases s with ⟨k, m⟩ | ⟨l, n⟩ <;> simp
    omega
open LaurentPolynomial in
abbrev leftSummand (n : ℕ) : (LaurentPolynomial ℚ)⟦X⟧ :=
  X ^ n.choose 2 * laurentZ ^ n * qPochhammerInf (X * X ^ n)
open LaurentPolynomial in
abbrev rightSummand (m : ℕ) : (LaurentPolynomial ℚ)⟦X⟧ :=
  X ^ (m.choose 2 + m) * laurentZInv ^ m * qPochhammerInv m
end JTP
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
end


