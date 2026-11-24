-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_DetPowUnitriB
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_DetPowUnitriB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:26:46.99565+00:00
-- url     : https://prove2.me/theorems/ccf9910e-080b-4f81-9cdd-664cd264a8b3
-- title:
--   Det Pow Unitri B
-- statement:
--   Definitions and structural lemmas for Det Pow Unitri B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/DetPowUnitriB.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace PI.WGB
open Formalism.BasicNotions MvPolynomial
def FiltB {σ : Type*} (ψ : σ → ℕ) (d : ℕ) : Submodule ℂ (MvPolynomial σ ℂ) where
  carrier := {g | ∀ e ∈ g.support, d ≤ Finsupp.weight ψ e}
  add_mem' := by
    intro a b ha hb e he
    classical
    rcases Finset.mem_union.mp (support_add he) with h1 | h1
    exacts [ha e h1, hb e h1]
  zero_mem' := by
    intro e he
    simp at he
  smul_mem' := by
    intro c a ha e he
    exact ha e (support_smul he)
def GoodB {σ : Type*} (R : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ) (ψ : σ → ℕ) (p : MvPolynomial σ ℂ) (d : ℕ) :
    Prop :=
  p ∈ FiltB ψ d ∧ R p - p ∈ FiltB ψ (d + 1)
section Good
variable {σ : Type*} (R : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ) (ψ : σ → ℕ)
end Good
end PI.WGB


