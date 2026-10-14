-- Prove2me | solution 1 for ActuarialValuation.jlProbability_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T06:29:16.954534+00:00
-- url     : https://prove2.me/submissions/d2624d28-eb5f-4a6a-9110-60f4250e62cf

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
theorem solution (px py : ℝ) (hx0 : 0≤px) (hx1 : px≤1) (hy0 : 0≤py) (hy1 : py≤1) (s : Fin 4) : 0≤jlProbability px py s := by
  classical

  have hx : 0 ≤ 1-px := sub_nonneg.mpr hx1
  have hy : 0 ≤ 1-py := sub_nonneg.mpr hy1
  fin_cases s <;> simp [jlGuaranteedPayment, jlReversionaryPayment, jlMortalityProfit, jlActualStrain, jlExpectedStrain, jlProbability, jlStateStrain, jlPostPremiumFund, jlOutcomeBenefit, jlOutcomeReserve, jlFirstDeath, jlAtLeastOneAlive, jlBothDead, jlOnlyYAlive, jlOnlyXAlive, jlBothAlive, Fin.sum_univ_succ] <;> positivity

#print axioms solution
