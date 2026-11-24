-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInverseOneAddPreservingAdelicCompletion
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInverseOneAddPreservingAdelicCompletion
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:43:44.220103+00:00
-- url     : https://prove2.me/theorems/01a25233-c8ef-47f7-8669-25dcaafae8e9
-- title:
--   Exists Inverse One Add Preserving Adelic Completion
-- statement:
--   Definitions and structural lemmas for Exists Inverse One Add Preserving Adelic Completion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsInverseOneAddPreservingAdelicCompletion.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
namespace GlobalTheory.UnRep.Nakayama
variable (F : Type) [Field F] [NumberField F]
def intAdeles : Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers F}
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem (v.adicCompletionIntegers F)
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem (v.adicCompletionIntegers F)
  neg_mem' ha v := neg_mem (ha v)
variable {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}
end GlobalTheory.UnRep.Nakayama


