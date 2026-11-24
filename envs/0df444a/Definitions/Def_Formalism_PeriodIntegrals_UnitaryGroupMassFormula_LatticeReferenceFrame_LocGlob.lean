-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_LocGlob
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_LocGlob
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T12:56:40.23737+00:00
-- url     : https://prove2.me/theorems/23e56765-a822-4918-9722-6d5a7a7053a3
-- title:
--   Loc Glob
-- statement:
--   Definitions and structural lemmas for Loc Glob, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/LocGlob.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
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
open scoped TensorProduct nonZeroDivisors
namespace PI.ScRefExists.LG
section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def lam (a : E) : E →ₗ[F] F := (Algebra.trace F E) ∘ₗ (LinearMap.mulLeft F a)
def Phi (a : E) : E ⊗[F] Af F →ₗ[F] Af F :=
  (TensorProduct.lid F (Af F)).toLinearMap ∘ₗ TensorProduct.map (lam a) LinearMap.id
def Gens : Submonoid (E ⊗[F] Af F) where
  carrier := {x | ∃ o : 𝓞 E, ∃ c ∈ Formalism.UG.intAd F, x = (algebraMap (𝓞 E) E o) ⊗ₜ[F] c}
  one_mem' := ⟨1, 1, one_mem _, by simp [Algebra.TensorProduct.one_def]⟩
  mul_mem' := by
    rintro _ _ ⟨o, c, hc, rfl⟩ ⟨o', c', hc', rfl⟩
    exact ⟨o * o', c * c', mul_mem hc hc', by simp [Algebra.TensorProduct.tmul_mul_tmul]⟩
end Gen
end PI.ScRefExists.LG


