-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentOfExponentBound
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentOfExponentBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:18.430802+00:00
-- url     : https://prove2.me/theorems/ed918730-aec1-47e8-836d-fba27e9974f8
-- title:
--   Clears Idempotent Of Exponent Bound
-- statement:
--   Definitions and structural lemmas for Clears Idempotent Of Exponent Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClearsIdempotentOfExponentBound.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
namespace GlobalTheory.Proof.clears_idempotent_of_exponent_bound
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory.Proof.clears_idempotent_of_exponent_bound
namespace GlobalTheory.Proof.clears_idempotent_of_exponent_bound
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory.Proof.clears_idempotent_of_exponent_bound
namespace GlobalTheory.Proof.clears_idempotent_of_exponent_bound
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem mul_mem_orderC {𝔣 : Ideal (OF E)} {c : OF E} (hc : c ∈ 𝔣) {x : E} (hx : x ∈ orderC (⊤ : Ideal (OF E))) :
    algebraMap (OF E) E c * x ∈ orderC 𝔣 := by
  obtain ⟨a, b, -, rfl⟩ := mem_orderC.1 hx
  refine mem_orderC.2 ⟨c * a, algebraMap (OF E) (𝓞 E) c * b,
    Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc), ?_⟩
  have hc' : ∀ a : OF E, algebraMap (OF E) E a = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a) := fun a => rfl
  rw [mul_add, map_mul, map_mul, ← hc' c]
def mulMap {𝔣 : Ideal (OF E)} {c : OF E} (hc : c ∈ 𝔣) : orderC (⊤ : Ideal (OF E)) →ₗ[ℤ] orderC 𝔣 where
  toFun x := ⟨algebraMap (OF E) E c * x, mul_mem_orderC hc x.2⟩
  map_add' x y := Subtype.ext (by simp [mul_add])
  map_smul' n x := Subtype.ext (by simp [mul_left_comm])
end GlobalTheory.Proof.clears_idempotent_of_exponent_bound


