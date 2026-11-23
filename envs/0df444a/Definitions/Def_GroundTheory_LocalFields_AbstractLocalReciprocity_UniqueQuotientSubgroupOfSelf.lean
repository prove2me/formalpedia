-- Prove2me | Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
-- name    : GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:20:01.113537+00:00
-- url     : https://prove2.me/theorems/be470ba1-7fbd-476c-8475-1455c48789d0
-- title:
--   Unique Quotient Subgroup Of Self
-- statement:
--   Definitions and structural lemmas for Unique Quotient Subgroup Of Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/UniqueQuotientSubgroupOfSelf.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.LocalField.Abstract
variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
section Self
variable (K : Subgroup G)
instance uniqueQuotientSubgroupOfSelf : Unique (K ⧸ K.subgroupOf K) where
  default := ((1 : K) : K ⧸ K.subgroupOf K)
  uniq q := by
    induction q using QuotientGroup.induction_on with
    | H σ =>
      rw [QuotientGroup.eq]
      simp
instance finiteIndex_subgroupOf_self : (K.subgroupOf K).FiniteIndex :=
  ⟨by simp [Subgroup.subgroupOf_self]⟩
end Self
section Pow
variable {K L : Subgroup G} [(L.subgroupOf K).FiniteIndex]
end Pow
section Transitivity
variable {K L M : Subgroup G}
def cosetShift (hLK : L ≤ K) (σ : K) : L ⧸ M.subgroupOf L → K ⧸ M.subgroupOf K :=
  Quotient.map' (fun τ : L => σ * (⟨τ, hLK τ.2⟩ : K)) fun τ τ' h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    simpa [Subgroup.mem_subgroupOf, mul_assoc] using h
@[simp] theorem cosetShift_mk (hLK : L ≤ K) (σ : K) (τ : L) :
    cosetShift (M := M) hLK σ (τ : L ⧸ M.subgroupOf L) =
      ((σ * (⟨τ, hLK τ.2⟩ : K) : K) : K ⧸ M.subgroupOf K) :=
  rfl
end Transitivity
section Conjugation
variable {K L : Subgroup G}
def cosetConj (σ : G) :
    K ⧸ L.subgroupOf K →
      K.map (MulAut.conj σ).toMonoidHom ⧸
        (L.map (MulAut.conj σ).toMonoidHom).subgroupOf (K.map (MulAut.conj σ).toMonoidHom) :=
  Quotient.map' (fun τ : K => (⟨σ * τ * σ⁻¹, τ, τ.2, rfl⟩ : K.map (MulAut.conj σ).toMonoidHom))
    fun τ τ' h => by
      rw [QuotientGroup.leftRel_apply] at h ⊢
      rw [Subgroup.mem_subgroupOf] at h ⊢
      refine ⟨(τ : G)⁻¹ * τ', by simpa using h, ?_⟩
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
end Conjugation
end GroundTheory.LocalField.Abstract


