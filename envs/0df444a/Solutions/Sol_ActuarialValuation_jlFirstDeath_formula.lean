-- Prove2me | solution 1 for ActuarialValuation.jlFirstDeath_formula
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T06:31:05.125669+00:00
-- url     : https://prove2.me/submissions/bb022d03-0ea5-4950-b541-a41a664ac500

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
theorem solution (px py : ℝ) : jlFirstDeath px py=1-px*py := by
  classical

  simp [jlGuaranteedPayment, jlReversionaryPayment, jlMortalityProfit, jlActualStrain, jlExpectedStrain, jlProbability, jlStateStrain, jlPostPremiumFund, jlOutcomeBenefit, jlOutcomeReserve, jlFirstDeath, jlAtLeastOneAlive, jlBothDead, jlOnlyYAlive, jlOnlyXAlive, jlBothAlive, Fin.sum_univ_succ] <;> ring

#print axioms solution
