-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftEqvDiv
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftEqvDiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:38:32.21408+00:00
-- url     : https://prove2.me/theorems/0c917bf0-fff4-4197-8d55-b1d1718fcced
-- title:
--   Lift Eqv Div
-- statement:
--   Definitions and structural lemmas for Lift Eqv Div, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvDiv.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Theorems.Thm_Formalism_UG_P_wlocal_E_mul_E
import Theorems.Thm_Formalism_UG_P_wlocal_E_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
section SlopeTestRemainingChoices
def tvU {r : ℕ} (a b : Fin r) (hab : a ≠ b) (t : ℂ) : GL (Fin r) ℂ where
  val := Formalism.UG.P.wlocal_E a b t
  inv := Formalism.UG.P.wlocal_E a b (-t)
  val_inv := by
    rw [Formalism.UG.P.wlocal_E_mul_E, if_neg hab, add_neg_cancel, add_zero, Formalism.UG.P.wlocal_E_zero]
  inv_val := by
    rw [Formalism.UG.P.wlocal_E_mul_E, if_neg hab, neg_add_cancel, add_zero, Formalism.UG.P.wlocal_E_zero]
end SlopeTestRemainingChoices
end PI.WGL


