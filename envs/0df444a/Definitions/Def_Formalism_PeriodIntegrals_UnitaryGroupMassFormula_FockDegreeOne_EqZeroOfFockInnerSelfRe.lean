-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:12.550932+00:00
-- url     : https://prove2.me/theorems/41804bb5-5bc2-4ca2-a0b6-73895d381c55
-- title:
--   Eq Zero Of Fock Inner Self Re
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Fock Inner Self Re, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/EqZeroOfFockInnerSelfRe.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Theorems.Thm_FockRaiseLowInner_fockInner_X_mul
import Theorems.Thm_FockRaiseLowInner_fockInner_add_left
import Theorems.Thm_FockRaiseLowInner_fockInner_add_right
import Theorems.Thm_FockRaiseLowInner_fockInner_eq_support
import Theorems.Thm_FockRaiseLowInner_fockInner_mul_X
import Theorems.Thm_FockRaiseLowInner_fockInner_neg_left
import Theorems.Thm_FockRaiseLowInner_fockInner_neg_right
import Theorems.Thm_FockRaiseLowInner_fockInner_smul_left
import Theorems.Thm_FockRaiseLowInner_fockInner_smul_right
import Theorems.Thm_FockRaiseLowInner_fockInner_sub_right
import Theorems.Thm_FockRaiseLowInner_fockInner_sum_left
import Theorems.Thm_FockRaiseLowInner_fockInner_sum_right
import Theorems.Thm_FockRaiseLowInner_fockInner_swap
import Theorems.Thm_FockRaiseLowInner_fockInner_zero_left
import Theorems.Thm_FockRaiseLowInner_fockInner_zero_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial FockH1Action FockRaiseLowInner
namespace PI.FockOneDegW.Inner
export FockRaiseLowInner (fockInner_X_mul fockInner_mul_X fockInner_sum_left fockInner_sum_right
  fockInner_swap fockInner_zero_left fockInner_zero_right fockInner_add_left fockInner_add_right
  fockInner_smul_left fockInner_smul_right fockInner_neg_left fockInner_neg_right fockInner_sub_right
  fockInner_eq_support wt)
section Pos
variable {σ : Type*}
def wtN (α : σ →₀ ℕ) : ℕ := α.prod (fun _ k => k.factorial)
end Pos
end PI.FockOneDegW.Inner
namespace PI.FockOneDegW
end PI.FockOneDegW


