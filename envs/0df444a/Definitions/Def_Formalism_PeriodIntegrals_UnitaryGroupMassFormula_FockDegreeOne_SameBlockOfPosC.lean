-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_SameBlockOfPosC
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_SameBlockOfPosC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:03.037979+00:00
-- url     : https://prove2.me/theorems/f7654a96-9c21-43a8-9ea2-015a534aae83
-- title:
--   Same Block Of Pos C
-- statement:
--   Definitions and structural lemmas for Same Block Of Pos C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/SameBlockOfPosC.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_RaisingLoweringSplit
import Theorems.Thm_FockRaiseLowInner_fockInner_add_right
import Theorems.Thm_FockRaiseLowInner_fockInner_smul_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial FockRaiseLowInner
namespace PI.FockOneDegW
def harmSub (hS : HarmSub) (p q r s : ℕ) : Submodule ℂ (Pol p q r s) where
  carrier := {P | Harm2 P}
  zero_mem' := (hS p q r s).1
  add_mem' := fun ha hb => (hS p q r s).2.1 _ _ ha hb
  smul_mem' := fun c _ h => (hS p q r s).2.2 c _ h
def innerL {σ : Type} (x : MvPolynomial σ ℂ) : MvPolynomial σ ℂ →ₗ[ℂ] ℂ where
  toFun Q := fockInner x Q
  map_add' Q Q' := fockInner_add_right x Q Q'
  map_smul' c Q := by simp [fockInner_smul_right]
end PI.FockOneDegW


