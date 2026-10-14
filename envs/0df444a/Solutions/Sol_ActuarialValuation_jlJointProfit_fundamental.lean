-- Prove2me | solution 1 for ActuarialValuation.jlJointProfit_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T06:18:32.94555+00:00
-- url     : https://prove2.me/submissions/b2ea8275-ec99-4d96-91a2-60909d965244

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
theorem solution (px py : ℝ) (pay next : Fin 4 → ℝ) (reserve premium interest : ℝ) (hx0 : 0≤px) (hx1 : px≤1) (hy0 : 0≤py) (hy1 : py≤1) : ((∑ s : Fin 4, jlProbability px py s)=1) ∧ ((∑ s : Fin 4, jlProbability px py s*jlMortalityProfit px py pay next (jlPostPremiumFund reserve premium interest) s)=0) ∧ (jlAtLeastOneAlive px py=px+py-px*py) := by
  classical

  refine ⟨?_, ?_, ?_⟩ <;> simp [jlGuaranteedPayment, jlReversionaryPayment, jlMortalityProfit, jlActualStrain, jlExpectedStrain, jlProbability, jlStateStrain, jlPostPremiumFund, jlOutcomeBenefit, jlOutcomeReserve, jlFirstDeath, jlAtLeastOneAlive, jlBothDead, jlOnlyYAlive, jlOnlyXAlive, jlBothAlive, Fin.sum_univ_succ] <;> ring

#print axioms solution
