-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemAd
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemAd
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:20:43.886482+00:00
-- url     : https://prove2.me/theorems/f90f94e9-0463-4d6d-8843-e7152d2a2c49
-- title:
--   Idem Ad
-- statement:
--   Definitions and structural lemmas for Idem Ad, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/IdemAd.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemLiftOfSteps
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
namespace PI.ScRefExists.Id
section Ad
variable {F : Type} [Field F] [NumberField F]
theorem memO {v : HeightOneSpectrum (𝓞 F)} {x : v.adicCompletion F} :
    x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1 := by
  first
    | exact Iff.rfl
    | exact HeightOneSpectrum.mem_adicCompletionIntegers F v
    | simp [HeightOneSpectrum.mem_adicCompletionIntegers]
def evA (v : HeightOneSpectrum (𝓞 F)) : Af F →+* v.adicCompletion F where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
def mkA (c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F) (hc : ∀ v, Valued.v (c v) ≤ 1) :
    Af F :=
  ⟨c, Filter.Eventually.of_forall fun v => memO.2 (hc v)⟩
end Ad
end PI.ScRefExists.Id


