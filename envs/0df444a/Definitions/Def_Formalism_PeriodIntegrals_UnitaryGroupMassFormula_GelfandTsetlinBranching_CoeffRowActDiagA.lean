-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_CoeffRowActDiagA
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_CoeffRowActDiagA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:03.73273+00:00
-- url     : https://prove2.me/theorems/3dd4c924-96e1-47c2-9acb-c62c50b30f51
-- title:
--   Coeff Row Act Diag A
-- statement:
--   Definitions and structural lemmas for Coeff Row Act Diag A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/CoeffRowActDiagA.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFactsProofA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetEmbUnitriA
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
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
variable {n : ℕ}
def elemGL_A (a b : Fin n) (hab : a ≠ b) (t : ℂ) : GL (Fin n) ℂ where
  val := 1 + Matrix.single a b t
  inv := 1 - Matrix.single a b t
  val_inv := by
    have h : Matrix.single a b t * Matrix.single a b t = 0 := by simp [Ne.symm hab]
    rw [add_mul, one_mul, mul_sub, mul_one, h]
    abel
  inv_val := by
    have h : Matrix.single a b t * Matrix.single a b t = 0 := by simp [Ne.symm hab]
    rw [sub_mul, one_mul, mul_add, mul_one, h]
    abel
end PI.WGB


