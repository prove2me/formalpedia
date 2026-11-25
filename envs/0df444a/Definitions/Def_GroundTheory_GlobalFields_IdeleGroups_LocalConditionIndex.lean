-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalConditionIndex
-- name    : GroundTheory_GlobalFields_IdeleGroups_LocalConditionIndex
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:41:26.653962+00:00
-- url     : https://prove2.me/theorems/7a0d8579-14cb-4393-9f8c-d59d943bd032
-- title:
--   Local Condition Index
-- statement:
--   Definitions and structural lemmas for Local Condition Index, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalConditionIndex.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleGroups
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Theorems.Thm_GroundTheory_LocalField_ord_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open NumberField IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace IdeleGroup
def localSubgroup (S T : Set (HeightOneSpectrum (𝓞 K)))
    (H : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ)
    (H' : ∀ w : InfinitePlace K, Subgroup (w.Completion)ˣ) : Subgroup (IdeleGroup K) where
  carrier := {x | (∀ v ∈ S, finiteProj v x ∈ H v) ∧ (∀ w, infiniteProj w x ∈ H' w) ∧
    ∀ v ∉ S ∪ T, ord v x = 0}
  one_mem' := ⟨fun v _ ↦ by rw [map_one]; exact one_mem _, fun w ↦ by rw [map_one]; exact one_mem _,
    fun v _ ↦ ord_one v⟩
  mul_mem' {x y} hx hy := ⟨fun v hv ↦ by rw [map_mul]; exact mul_mem (hx.1 v hv) (hy.1 v hv),
    fun w ↦ by rw [map_mul]; exact mul_mem (hx.2.1 w) (hy.2.1 w),
    fun v hv ↦ by rw [ord_mul, hx.2.2 v hv, hy.2.2 v hv, add_zero]⟩
  inv_mem' {x} hx := ⟨fun v hv ↦ by rw [map_inv]; exact inv_mem (hx.1 v hv),
    fun w ↦ by rw [map_inv]; exact inv_mem (hx.2.1 w),
    fun v hv ↦ by rw [ord_inv, hx.2.2 v hv, neg_zero]⟩
variable (S T : Set (HeightOneSpectrum (𝓞 K)))
  (H : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ)
  (H' : ∀ w : InfinitePlace K, Subgroup (w.Completion)ˣ)
def localQuotientMap (S : Finset (HeightOneSpectrum (𝓞 K))) :
    sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T) →*
      (∀ v : S, (v.1.adicCompletion K)ˣ ⧸ H v.1) × (∀ w : InfinitePlace K, (w.Completion)ˣ ⧸ H' w) :=
  MonoidHom.prod
    (MonoidHom.pi fun v ↦ (QuotientGroup.mk' (H v.1)).comp ((finiteProj v.1).comp (sIdeles _).subtype))
    (MonoidHom.pi fun w ↦ (QuotientGroup.mk' (H' w)).comp ((infiniteProj w).comp (sIdeles _).subtype))
def powerSubgroup (n : ℕ) (S T : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (IdeleGroup K) :=
  localSubgroup S T (fun v ↦ (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range)
    (fun w ↦ (powMonoidHom n : (w.Completion)ˣ →* _).range)
end IdeleGroup
end
end GroundTheory.Global


