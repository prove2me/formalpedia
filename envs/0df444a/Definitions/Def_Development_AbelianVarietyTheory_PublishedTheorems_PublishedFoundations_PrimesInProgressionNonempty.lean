-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_PrimesInProgressionNonempty
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_PrimesInProgressionNonempty
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:30.607357+00:00
-- url     : https://prove2.me/theorems/94c68c1f-99b1-4a10-887b-af11dd950e18
-- title:
--   Primes In Progression Nonempty
-- statement:
--   Definitions and structural lemmas for Primes In Progression Nonempty, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/PrimesInProgressionNonempty.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.Published
def primesInProgression (a q : ℕ) : Set ℕ := {p | p.Prime ∧ p ≡ a [MOD q]}
noncomputable def leastPrimeMod (a q : ℕ) : ℕ := sInf (primesInProgression a q)
def Linnik : Prop :=
  ∃ C L : ℝ, 0 < C ∧ 0 < L ∧ ∀ a q : ℕ, 1 ≤ a → 1 ≤ q → a.Coprime q →
    (leastPrimeMod a q : ℝ) ≤ C * (q : ℝ) ^ L
end GlobalTheory.Published


