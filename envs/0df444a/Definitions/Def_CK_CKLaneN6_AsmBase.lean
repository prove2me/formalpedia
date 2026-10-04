-- Prove2me | Definitions.Def_CK_CKLaneN6_AsmBase
-- name    : CK_CKLaneN6_AsmBase
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T13:03:50.976324+00:00
-- url     : https://prove2.me/theorems/a5c8e415-1890-4f89-b05b-b6d6c3052a18
-- title:
--   Courtade–Kumar proof module `CKLaneN6.AsmBase` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.AsmBase` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.AsmBase` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.AsmBase (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/AsmBase.lean)

import Definitions.Def_CK_CKLaneN6_FamBase

-- ===== source module CKLaneN6.AsmBase =====
section

/-!
# Lane N6: tail-recursive path-list comparison for kernel decides

`pathsBeq` compares two lists of paths element by element with the recursive call in tail position, so
`decide +kernel` on `pathsBeq l1 l2 = true` runs iteratively in the kernel even for lists with thousands
of paths (`instDecidableEqList` nests the recursive call and exhausts the kernel stack there).
`pathsBeq_eq` turns a successful comparison into list equality.
-/

set_option autoImplicit false

namespace CKLaneN6

def pathsBeq : List (List ℕ) → List (List ℕ) → Bool
  | [], [] => true
  | a :: as, b :: bs => (a == b) && pathsBeq as bs
  | _, _ => false

theorem pathsBeq_eq : ∀ {l1 l2 : List (List ℕ)}, pathsBeq l1 l2 = true → l1 = l2
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
      simp only [pathsBeq, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1, pathsBeq_eq h.2]
  | [], _ :: _, h => by simp [pathsBeq] at h
  | _ :: _, [], h => by simp [pathsBeq] at h

end CKLaneN6

end


