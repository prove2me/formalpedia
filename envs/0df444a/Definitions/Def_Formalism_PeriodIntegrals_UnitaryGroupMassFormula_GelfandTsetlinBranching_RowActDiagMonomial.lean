-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:55.837461+00:00
-- url     : https://prove2.me/theorems/a9f7d68f-953e-4c63-87c6-f25a20c9f64e
-- title:
--   Row Act Diag Monomial
-- statement:
--   Definitions and structural lemmas for Row Act Diag Monomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RowActDiagMonomial.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFEqSumOfSubsetB
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
def wnB (n N : ℕ) : Fin N × Fin N → (Fin n → ℕ) :=
  fun v => if hv : v.1.1 < n then Pi.single (⟨v.1.1, hv⟩ : Fin n) 1 else 0
def prowB (n N : ℕ) (a : Fin N) : ℕ := if a.1 < n then n - a.1 else 0
def psiB (n N : ℕ) : Fin N × Fin N → ℕ := fun v => prowB n N v.1
def PsiB (n : ℕ) : (Fin n → ℕ) →+ ℕ where
  toFun m := ∑ j, (n - j.1) * m j
  map_zero' := by simp
  map_add' a b := by simp [mul_add, Finset.sum_add_distrib]
def chiB {n : ℕ} (t : Fin n → ℂ) (m : Fin n → ℕ) : ℂ := ∏ j, t j ^ m j
def dB (n N : ℕ) (t : Fin n → ℂ) : Fin N → ℂ := fun a => if ha : a.1 < n then t ⟨a.1, ha⟩ else 1
end PI.WGB


