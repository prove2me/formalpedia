-- Prove2me | solution 1 for ActuarialValuation.jlReversionaryPayment_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T06:20:13.300907+00:00
-- url     : https://prove2.me/submissions/7236bc08-c975-4be0-a39f-aa3e1e264de6

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
theorem solution (px py benefit : ℝ) (hx0 : px≤1) (hy0 : 0≤py) (hb : 0≤benefit) : 0≤jlReversionaryPayment px py benefit := by
  classical

  exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hx0) hy0) hb

#print axioms solution
