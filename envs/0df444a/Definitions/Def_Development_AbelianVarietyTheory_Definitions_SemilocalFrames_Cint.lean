-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
-- name    : Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T05:25:13.104601+00:00
-- url     : https://prove2.me/theorems/c5b66d57-5db3-4c69-80cb-15523e412bf3
-- title:
--   Cint
-- statement:
--   Definitions and structural lemmas for Cint, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/Cint.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace GlobalTheory.IdxInt
variable {W : Type} [AddCommGroup W]
def Fine (A : AddSubgroup W) (φ : W → ℂ) (B : AddSubgroup W) : Prop :=
  B ≤ A ∧ B.relIndex A ≠ 0 ∧ (∀ w, ∀ b ∈ B, φ (w + b) = φ w) ∧
    ((fun w => (QuotientAddGroup.mk w : W ⧸ B)) '' Function.support φ).Finite
def Nice (A : AddSubgroup W) (φ : W → ℂ) : Prop := ∃ B, Fine A φ B
def cint (A : AddSubgroup W) (φ : W → ℂ) : ℂ :=
  if h : Nice A φ then (∑ᶠ c : W ⧸ h.choose, φ c.out) / (h.choose.relIndex A : ℂ) else 0
def ind (P : W → Prop) : W → ℂ := fun w => if P w then 1 else 0
end GlobalTheory.IdxInt


