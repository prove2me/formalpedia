-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_DetSubMemOfConj
-- name    : Development_AbelianVarietyTheory_Proofs_HeightProofs_DetSubMemOfConj
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:44:16.881675+00:00
-- url     : https://prove2.me/theorems/9cdfd881-ca3e-4561-a144-46339f45d541
-- title:
--   Det Sub Mem Of Conj
-- statement:
--   Definitions and structural lemmas for Det Sub Mem Of Conj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/DetSubMemOfConj.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Theorems.Thm_GlobalTheory_AdLat_mul_mem_adelicCompletionOfElementSet_of_mul_mem
import Theorems.Thm_GlobalTheory_AdLat_one_tmul_mem_adelicCompletionOfElementSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TwistTie
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def intRing : Subring (RA F E) where
  carrier := hat1 F (Set.range (algebraMap (𝓞 E) E))
  mul_mem' := mul_mem_adelicCompletionOfElementSet_of_mul_mem F (by rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact ⟨x * y, map_mul _ _ _⟩)
  one_mem' := one_tmul_mem_adelicCompletionOfElementSet F ⟨1, map_one _⟩
  add_mem' := add_mem
  zero_mem' := zero_mem _
  neg_mem' := neg_mem
end GlobalTheory.TwistTie


