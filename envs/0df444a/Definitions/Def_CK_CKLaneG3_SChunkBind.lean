-- Prove2me | Definitions.Def_CK_CKLaneG3_SChunkBind
-- name    : CK_CKLaneG3_SChunkBind
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T08:20:59.017525+00:00
-- url     : https://prove2.me/theorems/8ad13d9e-720e-4e63-843b-25c043a52455
-- title:
--   Courtade–Kumar proof module `CKLaneG3.SChunkBind` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.SChunkBind` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.SChunkBind` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.SChunkBind (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/SChunkBind.lean)

import Definitions.Def_CK_CKLaneG3_SliceBind
import Definitions.Def_CK_CKLaneG3_SBind

-- ===== source module CKLaneG3.SChunkBind =====
section

/-!
# Lane G3b: per-chunk (subtree) binding lemmas for large (S) owner labels

The monolithic per-label walk over the whole 160,789-leaf `sTree` with a 59,175-entry certified list was
killed at 43 GB RSS (kernel).  Here the same per-label statement is assembled from per-chunk facts
(`CKLaneG3.fam_node` / `fam_root` along the `sTree` skeleton, `CKLaneG3.SBind`), each chunk walking only its
own subtree (≤ 4096 leaves) with only its own part of the certified list:

* `sub_family_of_range`  : a contiguous range `(L.drop a).take len` of a DFS-ordered certified list;
* `sub_family_of_slices` : a concatenation of shard slices (`CKLaneG3.sliceOf`).
Soundness depends on neither the range nor the runs (they only decide whether the kernel check succeeds).
-/

set_option autoImplicit false

universe u

namespace CKLaneG3

open CKLaneD

/-- Per-subtree binding from a contiguous range of a certified list. -/
theorem sub_family_of_range {Q : List ℕ → Prop} (T : PTree) (n : ℕ) (rpre : List ℕ) (L : List (List ℕ))
    (hL : ∀ p ∈ L, Q p) (a len : ℕ)
    (hc : (tconsume (fun l => l == n) T rpre ((L.drop a).take len)).isSome = true) :
    ∀ q ∈ T.leavesR rpre, q.2 = n → Q q.1 := by
  intro q hq hn
  obtain ⟨L', hL'⟩ := Option.isSome_iff_exists.mp hc
  have hm := (tconsume_spec T rpre hL').1 q hq (by simp [hn])
  exact hL _ (List.mem_of_mem_drop (List.mem_of_mem_take hm))

/-- Per-subtree binding from a concatenation of shard slices. -/
theorem sub_family_of_slices {α : Type u} {Q : List ℕ → Prop} (T : PTree) (n : ℕ) (rpre : List ℕ)
    (SH : List (List α)) (f : α → List ℕ) (hSH : ∀ S ∈ SH, ∀ x ∈ S, Q (f x)) (runs : List (ℕ × ℕ × ℕ))
    (hc : (tconsume (fun l => l == n) T rpre (((runs.map (sliceOf SH)).flatten).map f)).isSome = true) :
    ∀ q ∈ T.leavesR rpre, q.2 = n → Q q.1 := by
  intro q hq hn
  obtain ⟨L', hL'⟩ := Option.isSome_iff_exists.mp hc
  have hm := (tconsume_spec T rpre hL').1 q hq (by simp [hn])
  obtain ⟨x, hx, hxq⟩ := List.mem_map.mp hm
  obtain ⟨S, hS, hxS⟩ := mem_slices hx
  rw [← hxq]
  exact hSH S hS x hxS

end CKLaneG3

end


