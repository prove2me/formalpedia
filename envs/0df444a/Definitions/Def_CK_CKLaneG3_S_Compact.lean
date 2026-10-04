-- Prove2me | Definitions.Def_CK_CKLaneG3_S_Compact
-- name    : CK_CKLaneG3_S_Compact
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T19:21:16.114718+00:00
-- url     : https://prove2.me/theorems/bb4b1674-6b8e-49eb-97ce-575cd15d8baf
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.Compact` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.Compact` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.Compact` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.Compact (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/Compact.lean)

import Definitions.Def_CK_CKLaneG3_SCompact
import Definitions.Def_CK_CKLaneG3_PSort
import Definitions.Def_CK_CKLaneG3_S_STree

-- ===== source module CKLaneG3.S.Compact =====
section

/-!
# Lane G3: the canonical same-side tree and the route row `SS_Compact` (BRIEF §7, items (3), (4))

* `sTree_cover` : every law with `a ≤ b`, `b ≤ 1/2`, `1/16 < a + b`, `2^-32 < a/b` lies in the physical
  image `InS (sBox q.1)` of some archived (S) leaf `q ∈ sTree.leaves`.
* `ssCompact_of_leaves` : `SLeafOK` on every archived leaf box gives `SSCompactRow`
  (verbatim copy of `CKRoute.SS_Compact`).
* `ssCompact_of_labels` : the same from the nine per-label families
  `∀ q ∈ sTree.leaves, q.2 = n → SLeafOK (sBox q.1)` (labels 0..8, see `CKLaneG3.S.STree`).
* `sLabel_family_of_list` : per-label binding of a DFS-ordered certified path list to the leaves of
  `sTree` by one linear kernel walk (`CKLaneG3.label_family_of_consume`).
-/

set_option autoImplicit false

namespace CKLaneG3.S

open CKLaneD CKLaneG3 GeneralCK

/-- (3) Coverage of the `SS_Compact` row by the archived same-side leaves. -/
theorem sTree_cover {k : ℕ} (μ : InteriorLaw (Fin k)) (hab : μ.a ≤ μ.b) (hb : μ.b ≤ 1 / 2)
    (hm : 1 / 16 < μ.a + μ.b) (hr : 1 / 4294967296 < μ.a / μ.b) :
    ∃ q ∈ sTree.leaves, InS (sBox q.1) μ.a μ.b μ.meanEntropy :=
  sCover_of_tree sTree μ hab hb hm hr

/-- (4) The route row `SS_Compact` from the per-leaf obligation on every archived leaf. -/
theorem ssCompact_of_leaves (h : ∀ q ∈ sTree.leaves, SLeafOK (sBox q.1)) : SSCompactRow :=
  ssCompact_of_tree_leaves sTree h

/-- Per-label binding of a certified path list (DFS order) to the archived leaves of label `n`. -/
theorem sLabel_family_of_list (n : ℕ) (L : List (List ℕ)) (hL : ∀ p ∈ L, SLeafOK (sBox p))
    (hc : (tconsume (fun l => l == n) sTree [] L).isSome = true) :
    ∀ q ∈ sTree.leaves, q.2 = n → SLeafOK (sBox q.1) :=
  label_family_of_consume (Q := fun p => SLeafOK (sBox p)) sTree n L hL hc

/-- Per-label binding of an arbitrarily ordered certified path list (kernel merge sort with `fuel`
halving levels, then one linear walk). -/
theorem sLabel_family_of_unsorted (n fuel : ℕ) (L : List (List ℕ)) (hL : ∀ p ∈ L, SLeafOK (sBox p))
    (hc : (tconsume (fun l => l == n) sTree [] (psort fuel L)).isSome = true) :
    ∀ q ∈ sTree.leaves, q.2 = n → SLeafOK (sBox q.1) :=
  label_family_of_psort (Q := fun p => SLeafOK (sBox p)) sTree n fuel L hL hc

/-- The route row `SS_Compact` from the nine per-label leaf families. -/
theorem ssCompact_of_labels
    (h0 : ∀ q ∈ sTree.leaves, q.2 = 0 → SLeafOK (sBox q.1))
    (h1 : ∀ q ∈ sTree.leaves, q.2 = 1 → SLeafOK (sBox q.1))
    (h2 : ∀ q ∈ sTree.leaves, q.2 = 2 → SLeafOK (sBox q.1))
    (h3 : ∀ q ∈ sTree.leaves, q.2 = 3 → SLeafOK (sBox q.1))
    (h4 : ∀ q ∈ sTree.leaves, q.2 = 4 → SLeafOK (sBox q.1))
    (h5 : ∀ q ∈ sTree.leaves, q.2 = 5 → SLeafOK (sBox q.1))
    (h6 : ∀ q ∈ sTree.leaves, q.2 = 6 → SLeafOK (sBox q.1))
    (h7 : ∀ q ∈ sTree.leaves, q.2 = 7 → SLeafOK (sBox q.1))
    (h8 : ∀ q ∈ sTree.leaves, q.2 = 8 → SLeafOK (sBox q.1)) : SSCompactRow := by
  apply ssCompact_of_leaves
  intro q hq
  have hlt : q.2 < 9 := by
    have := all_of_tallLabels sTree [] sTree_labels_lt9 q hq
    simpa using this
  rcases q with ⟨p, l⟩
  simp only at hlt ⊢
  match l, hlt, hq with
  | 0, _, hq => exact h0 (p, 0) hq rfl
  | 1, _, hq => exact h1 (p, 1) hq rfl
  | 2, _, hq => exact h2 (p, 2) hq rfl
  | 3, _, hq => exact h3 (p, 3) hq rfl
  | 4, _, hq => exact h4 (p, 4) hq rfl
  | 5, _, hq => exact h5 (p, 5) hq rfl
  | 6, _, hq => exact h6 (p, 6) hq rfl
  | 7, _, hq => exact h7 (p, 7) hq rfl
  | 8, _, hq => exact h8 (p, 8) hq rfl
  | n + 9, h, _ => exact absurd h (by omega)

end CKLaneG3.S

end


