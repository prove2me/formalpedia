-- Prove2me | Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Reciprocity
-- name    : GroundTheory_LocalFields_AbstractLocalReciprocity_Reciprocity
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T02:12:54.073624+00:00
-- url     : https://prove2.me/theorems/4d5b1740-274c-565a-8bf6-c3c34eab64a6
-- title:
--   Reciprocity
-- statement:
--   Definitions and structural lemmas for Reciprocity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Reciprocity.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Unramified
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_range_valuation
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
import Theorems.Thm_GroundTheory_LocalField_Abstract_isOpen_frobeniusClosure
import Theorems.Thm_GroundTheory_LocalField_Abstract_mem_frobeniusClosure_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk


set_option autoImplicit false
namespace GroundTheory.LocalField.Abstract
open ProfiniteInteger
namespace ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  (D : ClassFieldData G A)
structure FrobeniusLift (K : OpenSubgroup G) where

  elt : G
  mem : elt ∈ (K : Subgroup G)

  deg : ℕ
  deg_pos : 0 < deg
  deg_eq : D.deg elt = Multiplicative.ofAdd ((deg * inertiaDegree D.deg K : ℕ) : ℤ̂)
variable {D} {K L : OpenSubgroup G}
namespace FrobeniusLift
omit [TotallyDisconnectedSpace G] in
theorem degree_ne_zero (s : D.FrobeniusLift K) : s.deg * inertiaDegree D.deg K ≠ 0 :=
  mul_ne_zero s.deg_pos.ne' (D.inertiaDegree_ne_zero K)
omit [TotallyDisconnectedSpace G] in

theorem mem_normalizer (hLK : L ≤ K) [hN : ((L : Subgroup G).subgroupOf K).Normal] {σ : G}
    (hσ : σ ∈ (K : Subgroup G)) :
    σ ∈ Subgroup.normalizer (((L : Subgroup G) ⊓ D.deg.ker : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hconj : ∀ g ∈ (K : Subgroup G), ∀ x ∈ (L : Subgroup G), g * x * g⁻¹ ∈ (L : Subgroup G) := by
    intro g hg x hx
    have := hN.conj_mem ⟨x, hLK hx⟩ (by simpa [Subgroup.mem_subgroupOf] using hx) ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf] using this
  simp only [Subgroup.mem_inf, MonoidHom.mem_ker, map_mul, map_inv]
  constructor
  · rintro ⟨hL, hk⟩
    refine ⟨hconj σ hσ h hL, ?_⟩
    rw [hk, mul_one, mul_inv_cancel]
  · rintro ⟨hL, hk⟩
    refine ⟨?_, ?_⟩
    · have := hconj σ⁻¹ (K.inv_mem hσ) _ hL
      simpa [mul_assoc] using this
    · have := hk
      rwa [mul_comm (D.deg σ), mul_assoc, mul_inv_cancel, mul_one] at this
variable (L) in

noncomputable def field (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    (s : D.FrobeniusLift K) : OpenSubgroup G where
  toSubgroup := frobeniusClosure D.deg L s.elt
  isOpen' := isOpen_frobeniusClosure D.continuous_deg L.isOpen (mem_normalizer hLK s.mem)
    s.degree_ne_zero s.deg_eq
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] (s : D.FrobeniusLift K)
theorem elt_mem_field : s.elt ∈ ((s.field L hLK : OpenSubgroup G) : Subgroup G) :=
  mem_frobeniusClosure_self
end FrobeniusLift
omit [TotallyDisconnectedSpace G] in

theorem exists_prime (K : OpenSubgroup G) :
    ∃ π : fixedModule A (K : Subgroup G), D.valuation K π = Multiplicative.ofAdd 1 := by
  have h := D.intCast_mem_range_val 1
  rw [← D.range_valuation K, Int.cast_one] at h
  exact h
section PrimeNorm
variable (K L) in

noncomputable def primeNorm (S : OpenSubgroup G) : tateZero A (K : Subgroup G) (L : Subgroup G) :=
  QuotientGroup.mk (norm A (K : Subgroup G) (S : Subgroup G) (D.exists_prime S).choose)
end PrimeNorm
section RecFrob
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
variable (L) in

noncomputable def recFrob (s : D.FrobeniusLift K) : tateZero A (K : Subgroup G) (L : Subgroup G) :=
  D.primeNorm K L (s.field L hLK)
end RecFrob
end ClassFieldData
end GroundTheory.LocalField.Abstract


