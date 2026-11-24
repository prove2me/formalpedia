-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_PsiTrCore
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_PsiTrCore
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:41:59.708162+00:00
-- url     : https://prove2.me/theorems/fc98a4d7-59f8-4845-83ce-e42191b50094
-- title:
--   Psi Tr Core
-- statement:
--   Definitions and structural lemmas for Psi Tr Core, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/PsiTrCore.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LevelCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_PsiTrCoreApprox
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_PsiTrCoreTrace
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
open scoped TensorProduct
namespace Formalism.L2.S.Pv.PsiTrCore
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem incl_mem (o : 𝓞 E) : Formalism.UG.inclE (F := F) (Af F) (o : E) ∈ IntAf F E := by
  show _ ∈ Formalism.UG.tensInt (F := F) (Af F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)
  unfold Formalism.UG.tensInt
  apply Subring.subset_closure
  left
  refine ⟨⟨(o : E), o, rfl⟩, ?_⟩
  simp [Formalism.UG.inclE]
def congSub (n : ℤ) : Subring (E ⊗[F] Af F) where
  carrier := {t | ∃ o : 𝓞 E, ∃ s ∈ IntAf F E,
    t = Formalism.UG.inclE (F := F) (Af F) (o : E) + (n : E ⊗[F] Af F) * s}
  zero_mem' := ⟨0, 0, zero_mem _, by simp [RingOfIntegers.coe_eq_algebraMap]⟩
  one_mem' := ⟨1, 0, zero_mem _, by simp [RingOfIntegers.coe_eq_algebraMap]⟩
  add_mem' := by
    rintro _ _ ⟨o, s, hs, rfl⟩ ⟨o', s', hs', rfl⟩
    refine ⟨o + o', s + s', add_mem hs hs', ?_⟩
    simp only [RingOfIntegers.coe_eq_algebraMap, map_add]
    ring
  neg_mem' := by
    rintro _ ⟨o, s, hs, rfl⟩
    refine ⟨-o, -s, neg_mem hs, ?_⟩
    simp only [RingOfIntegers.coe_eq_algebraMap, map_neg]
    ring
  mul_mem' := by
    rintro _ _ ⟨o, s, hs, rfl⟩ ⟨o', s', hs', rfl⟩
    refine ⟨o * o', Formalism.UG.inclE (F := F) (Af F) (o : E) * s' + s * Formalism.UG.inclE (F := F) (Af F) (o' : E) +
      (n : E ⊗[F] Af F) * s * s', ?_, ?_⟩
    · exact add_mem (add_mem (mul_mem (incl_mem o) hs') (mul_mem hs (incl_mem o')))
        (mul_mem (mul_mem (intCast_mem _ n) hs) hs')
    · simp only [RingOfIntegers.coe_eq_algebraMap, map_mul]
      ring
end Formalism.L2.S.Pv.PsiTrCore


