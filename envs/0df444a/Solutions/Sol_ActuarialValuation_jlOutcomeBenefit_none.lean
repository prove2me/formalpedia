-- Prove2me | solution 1 for ActuarialValuation.jlOutcomeBenefit_none
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T06:24:43.248089+00:00
-- url     : https://prove2.me/submissions/811581a0-6e71-4c4b-b74e-c2232be5da93

import Mathlib
import Definitions.Def_actuarial_jlGuaranteedPayment
import Definitions.Def_actuarial_jlReversionaryPayment
import Definitions.Def_actuarial_jlMortalityProfit
import Definitions.Def_actuarial_jlActualStrain
import Definitions.Def_actuarial_jlExpectedStrain
import Definitions.Def_actuarial_jlProbability
import Definitions.Def_actuarial_jlStateStrain
import Definitions.Def_actuarial_jlPostPremiumFund
import Definitions.Def_actuarial_jlOutcomeBenefit
import Definitions.Def_actuarial_jlOutcomeReserve
import Definitions.Def_actuarial_jlFirstDeath
import Definitions.Def_actuarial_jlAtLeastOneAlive
import Definitions.Def_actuarial_jlBothDead
import Definitions.Def_actuarial_jlOnlyYAlive
import Definitions.Def_actuarial_jlOnlyXAlive
import Definitions.Def_actuarial_jlBothAlive
set_option autoImplicit false
noncomputable section
open ActuarialValuation
theorem solution (a b c d : ℝ) : jlOutcomeBenefit a b c d 3=d := by
  classical

  simp [jlGuaranteedPayment, jlReversionaryPayment, jlMortalityProfit, jlActualStrain, jlExpectedStrain, jlProbability, jlStateStrain, jlPostPremiumFund, jlOutcomeBenefit, jlOutcomeReserve, jlFirstDeath, jlAtLeastOneAlive, jlBothDead, jlOnlyYAlive, jlOnlyXAlive, jlBothAlive, Fin.sum_univ_succ] <;> ring

#print axioms solution
