-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_IsEquivAdicAbvNormAbv
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_IsEquivAdicAbvNormAbv
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T03:07:36.76973+00:00
-- url     : https://prove2.me/theorems/6ea7c5aa-a5c0-5f7c-8270-57d44dd86d92
-- title:
--   Is Equiv Adic Abv Norm Abv
-- statement:
--   Definitions and structural lemmas for Is Equiv Adic Abv Norm Abv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionDegrees/IsEquivAdicAbvNormAbv.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_NormLeOneOfInteger
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
namespace PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc
noncomputable def normAbv {l : ℕ} [Fact l.Prime] {E : Type} [Field E] (φ : E →+* Om l) :
    AbsoluteValue E ℝ where
  toFun x := ‖φ x‖
  map_mul' x y := by simp
  nonneg' x := norm_nonneg _
  eq_zero' x := by simp
  add_le' x y := by simpa using norm_add_le (φ x) (φ y)
end PI.CompDegEF


