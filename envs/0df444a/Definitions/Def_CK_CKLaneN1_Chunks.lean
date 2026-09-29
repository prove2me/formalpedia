-- Prove2me | Definitions.Def_CK_CKLaneN1_Chunks
-- name    : CK_CKLaneN1_Chunks
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:52:12.763126+00:00
-- url     : https://prove2.me/theorems/66547242-49c0-4230-afff-89780a377806
-- title:
--   Courtade–Kumar proof module `CKLaneN1.Chunks` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.Chunks` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.Chunks` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.Chunks (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/Chunks.lean)

import Definitions.Def_CK_CKLaneN1_Tree

-- ===== source module CKLaneN1.Chunks =====
section

/-!
# Lane N1: chunked list checks

`all_of_chunks` assembles a whole-list Boolean check from fixed-length chunk checks (one fleet
shard per chunk), so the aggregators never re-evaluate the leaf checks.
-/

namespace CKLaneN1

/-- A list satisfies `f` everywhere if each of its `m` chunks of length `N` does. -/
theorem all_of_chunks {α : Type} (f : α → Bool) (N : ℕ) :
    ∀ (m : ℕ) (l : List α), l.length ≤ N * m →
      (∀ k < m, ((l.drop (N * k)).take N).all f = true) → l.all f = true
  | 0, l, hlen, _ => by
      have hl : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      simp [hl]
  | m + 1, l, hlen, h => by
      have h0 := h 0 (Nat.succ_pos m)
      simp only [Nat.mul_zero, List.drop_zero] at h0
      have hrest : (l.drop N).all f = true := by
        apply all_of_chunks f N m (l.drop N)
        · simp only [List.length_drop]
          rw [Nat.mul_succ] at hlen
          omega
        · intro k hk
          have hk' := h (k + 1) (by omega)
          rw [List.drop_drop]
          rw [show N + N * k = N * (k + 1) by ring]
          exact hk'
      rw [← List.take_append_drop N l, List.all_append, h0, hrest]
      rfl

end CKLaneN1

end


