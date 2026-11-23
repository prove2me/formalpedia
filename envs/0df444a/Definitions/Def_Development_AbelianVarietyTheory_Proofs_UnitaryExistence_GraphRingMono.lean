-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GraphRingMono
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GraphRingMono
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:41.718983+00:00
-- url     : https://prove2.me/theorems/424f5e3a-8e90-47f8-b1c9-5e62ce1d3cc3
-- title:
--   Graph Ring Mono
-- statement:
--   Definitions and structural lemmas for Graph Ring Mono, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GraphRingMono.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
namespace GlobalTheory.PBasis
variable {k : Type} [Field k]
def graphRing (p : ℕ) {Q : Type} [CommRing Q] (f : k →+* Q) (g : k → Q) (B : Set k) :
    Subring (k × Q) :=
  Subring.closure (Set.range (fun x : k => (x ^ p, f x)) ∪ (fun b => (b, g b)) '' B)
def Indep (p : ℕ) (B : Set k) : Prop :=
  ∀ (Q : Type) [CommRing Q] (f : k →+* Q) (g : k → Q), (∀ b ∈ B, g b ^ p = f b) →
    ∀ z ∈ graphRing p f g B, z.1 = 0 → z.2 = 0
def powField {p : ℕ} (hp : p ≠ 0) (B : Set k) : Subfield k where
  toSubring := Subring.closure (Set.range (fun x : k => x ^ p) ∪ B)
  inv_mem' := by
    intro x hx
    change x ∈ Subring.closure (Set.range (fun x : k => x ^ p) ∪ B) at hx
    change x⁻¹ ∈ Subring.closure (Set.range (fun x : k => x ^ p) ∪ B)
    rcases eq_or_ne x 0 with rfl | hx0
    · simpa using hx
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
    have : x⁻¹ = x ^ n * (x⁻¹) ^ (n + 1) := by
      rw [pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hx0]; simp
    rw [this]
    exact mul_mem (pow_mem hx n) (Subring.subset_closure (Or.inl ⟨x⁻¹, rfl⟩))
end GlobalTheory.PBasis


