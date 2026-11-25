-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsUnitMatrixOfPowSmulSpanInvert
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsUnitMatrixOfPowSmulSpanInvert
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T01:44:22.302798+00:00
-- url     : https://prove2.me/theorems/a22fc732-d64b-42d4-8ed4-966599e52314
-- title:
--   Exists Is Unit Matrix Of Pow Smul Span Invert
-- statement:
--   Definitions and structural lemmas for Exists Is Unit Matrix Of Pow Smul Span Invert, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIsUnitMatrixOfPowSmulSpanInvert.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
def powDenomSubring {S EE : Type} [CommRing S] [CommRing EE] (a : S →+* EE) (Q : S) :
    Subring EE where
  carrier := {e | ∃ (n : ℕ) (t : S), a Q ^ n * e = a t}
  mul_mem' := by
    rintro e f ⟨n, t, ht⟩ ⟨m, r, hr⟩
    refine ⟨n + m, t * r, ?_⟩
    rw [map_mul, ← ht, ← hr]; ring
  one_mem' := ⟨0, 1, by simp⟩
  add_mem' := by
    rintro e f ⟨n, t, ht⟩ ⟨m, r, hr⟩
    refine ⟨n + m, Q ^ m * t + Q ^ n * r, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, ← ht, ← hr]; ring
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro e ⟨n, t, ht⟩
    refine ⟨n, -t, ?_⟩
    rw [map_neg, ← ht]; ring
end GlobalTheory


