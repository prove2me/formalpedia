-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_StabiliserCardinality
-- name    : Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_StabiliserCardinality
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T08:49:29.744794+00:00
-- url     : https://prove2.me/theorems/3c2be817-56f1-5aa2-96f1-4d1d3ef94edb
-- title:
--   Stabiliser Cardinality
-- statement:
--   Definitions and structural lemmas for Stabiliser Cardinality, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/StabiliserCardinality.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.IndefiniteRowSideFullHecke.StabiliserCardinality
def stab {G : Type} [Group G] (Γ K : Subgroup G) (y : G) : Subgroup G :=
  Γ ⊓ K.map (MulAut.conj y).toMonoidHom
theorem mem_stab {G : Type} [Group G] (Γ K : Subgroup G) (y γ : G) :
    γ ∈ stab Γ K y ↔ γ ∈ Γ ∧ y⁻¹ * γ * y ∈ K := by
  unfold stab
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨_, h, by simp [mul_assoc]⟩⟩
  rintro ⟨k, hk, rfl⟩
  simpa [mul_assoc] using hk
def DoubleCosetCount : Prop :=
  ∀ (G : Type) [Group G] (Γ U K : Subgroup G), U ≤ K →
    (U.subgroupOf K).FiniteIndex →
    ∀ [Fintype (DoubleCoset.Quotient (Γ : Set G) (K : Set G))],
    (∀ y : G, Finite (stab Γ K y)) →
    (∀ x : G, stab Γ U x = ⊥) →
    ∀ rep : DoubleCoset.Quotient (Γ : Set G) (K : Set G) → G,
      (∀ c, DoubleCoset.mk Γ K (rep c) = c) →
      Finite (DoubleCoset.Quotient (Γ : Set G) (U : Set G)) ∧
      (Nat.card (DoubleCoset.Quotient (Γ : Set G) (U : Set G)) : ℚ) =
        (U.relIndex K : ℚ) *
          ∑ c : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
            1 / (Nat.card (stab Γ K (rep c)) : ℚ)
example {G : Type} [Group G] (Γ : Subgroup G) (x : G) : stab Γ ⊥ x = ⊥ := by
  simp [stab]
example {G : Type} [Group G] (Γ : Subgroup G) (x : G) : stab Γ ⊤ x = Γ := by
  ext γ; simp [mem_stab]
example {G : Type} [Group G] (Γ K : Subgroup G) :
    ∀ c : DoubleCoset.Quotient (Γ : Set G) (K : Set G), DoubleCoset.mk Γ K c.out = c :=
  DoubleCoset.out_eq' Γ K
end GlobalTheory.IndefiniteRowSideFullHecke.StabiliserCardinality


