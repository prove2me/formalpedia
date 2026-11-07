-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
-- name    : OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:42:59.075961+00:00
-- url     : https://prove2.me/theorems/100080a0-9f32-4278-84d4-faf77a0c9586
-- title:
--   Theta Local Rows
-- statement:
--   Definitions and structural lemmas for Theta Local Rows, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ThetaLocalRows.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
import Theorems.Thm_OAI_ActualEisensteinCoordinates_unique_coordinates
import Theorems.Thm_OAI_ActualEisensteinCubic_qNat_eq_absNorm_span
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftLatticeCount_coords_eval
import Theorems.Thm_OAI_ShortDraftLatticeCount_qNat_mul
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


set_option autoImplicit false
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
namespace ActualEisensteinCubic
section
open EisensteinEmbedding ConcreteTraceCRT Complex
open EisensteinEmbedding ConcreteTraceCRT Complex
open scoped Topology
open Filter
noncomputable def actualVariableDualKernel (a b : ℤ) (η : ℝ) (y : O) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
    (‖eisEmbedding y‖ ^ 2 : ℂ)) *
  ShortDraftTrace.breveE
    (eisEmbedding (-(ActualEisensteinCoordinates.eval a b * y^2)) /
      eisLam /
      ((4 * OscSpecial.r η (a : ℝ) (b : ℝ) : ℝ) : ℂ))
noncomputable def actualFixedDualKernel (a b : ℤ) (η : ℝ) (y : O) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
    (‖eisEmbedding y‖ ^ 2 : ℂ)) *
  fixedDualPhase (ActualEisensteinCoordinates.eval a b) y
end
section
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex
end
section
open EisensteinEmbedding ConcreteTraceCRT Complex
end
section
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex
end
section
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex
end
end ActualEisensteinCubic
theorem theta_counter_lambda_eq : ActualEisensteinCubic.lambda =
    ActualEisensteinCoordinates.eval (-1) 1 := by
  have homega : ActualEisensteinCubic.omega = ActualEisensteinCoordinates.omega := by
    rfl
  rw [ActualEisensteinCubic.lambda, ActualEisensteinCoordinates.eval, homega]
  ring
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
noncomputable def pSeven : ActualEisensteinCubic.O := ActualEisensteinCoordinates.eval 1 3
noncomputable def PSeven : Ideal ActualEisensteinCubic.O := Ideal.span {pSeven}
theorem pSeven_norm : ShortDraftLatticeCount.qNat pSeven = 7 := by
  unfold ShortDraftLatticeCount.qNat pSeven
  rw [ShortDraftLatticeCount.coords_eval]
  norm_num [ShortDraftLatticeCount.q] <;> rfl
theorem pSeven_ne : pSeven ≠ 0 := by
  intro h
  have hh : ActualEisensteinCoordinates.eval 1 3 = ActualEisensteinCoordinates.eval 0 0 := by
    simpa [pSeven, ActualEisensteinCoordinates.eval] using h
  have := (ActualEisensteinCoordinates.unique_coordinates hh).1
  omega
theorem PSeven_absNorm : Ideal.absNorm PSeven = 7 := by
  simpa only [PSeven, ActualEisensteinCubic.qNat_eq_absNorm_span] using pSeven_norm
theorem PSeven_maximal : PSeven.IsMaximal := by
  have hprime : PSeven.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by
    rw [PSeven_absNorm, Nat.irreducible_iff_nat_prime]
    exact (by decide : Nat.Prime 7))
  apply hprime.isMaximal
  exact Ideal.span_singleton_eq_bot.not.mpr pSeven_ne
theorem lambda7_norm :
    ShortDraftLatticeCount.qNat (ActualEisensteinCoordinates.eval (-1) 1) = 3 := by
  unfold ShortDraftLatticeCount.qNat
  rw [ShortDraftLatticeCount.coords_eval]
  norm_num [ShortDraftLatticeCount.q] <;> rfl
noncomputable def thetaGammaSeven : ℂ := by
  letI : PSeven.IsMaximal := PSeven_maximal
  exact breveGamma2 PSeven
    (by
      rw [theta_counter_lambda_eq]
      intro hh
      obtain ⟨x, hx⟩ := Ideal.mem_span_singleton.mp hh
      have hnorm := congrArg ShortDraftLatticeCount.qNat hx
      rw [ShortDraftLatticeCount.qNat_mul, pSeven_norm, lambda7_norm] at hnorm
      omega)
    pSeven rfl pSeven_ne
open MulChar AddChar
namespace ShortDraftLocal
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end ShortDraftLocal
end
end OAI


