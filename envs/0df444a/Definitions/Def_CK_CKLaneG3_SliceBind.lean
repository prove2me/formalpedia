-- Prove2me | Definitions.Def_CK_CKLaneG3_SliceBind
-- name    : CK_CKLaneG3_SliceBind
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T00:44:41.100766+00:00
-- url     : https://prove2.me/theorems/271051d0-0b11-448d-a29b-971e2de538d8
-- title:
--   Courtade–Kumar proof module `CKLaneG3.SliceBind` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.SliceBind` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.SliceBind` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.SliceBind (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/SliceBind.lean)

import Definitions.Def_CK_CKLaneG3_S_Compact

-- ===== source module CKLaneG3.SliceBind =====
section

/-!
# Lane G3b: per-label binding by shard slices (no in-kernel sorting)

`sLabel_family_of_unsorted` sorts the lane's certified list in the kernel (`psort`); measured cost for
3,205 paths ≈ 340 s / 13 GB, which does not scale to the 7,657 – 59,175-path labels.  Here the DFS-ordered
list is instead assembled from SLICES of the lane's own shard lists:

* `SH : List (List α)` — the lane's shard lists (e.g. `[Fleet.S0000.certs, …]`), `f : α → List ℕ` the
  path projection, `hSH` — every shard entry satisfies the leaf obligation (from the shard theorems);
* `runs : List (ℕ × ℕ × ℕ)` — data only: `(k, i, len)` = `len` consecutive entries of shard `k` from
  position `i` (computed offline so that the concatenation is the label's leaves in DFS order);
* soundness (`mem_slices`) needs no bound checks: an out-of-range slice is just shorter / empty, which can
  only make the kernel consumer check fail, never succeed wrongly.
-/

set_option autoImplicit false

universe u

namespace CKLaneG3

/-- The slice `(k, i, len)` of a list of shard lists. -/
def sliceOf {α : Type u} (SH : List (List α)) (r : ℕ × ℕ × ℕ) : List α :=
  ((SH.getD r.1 []).drop r.2.1).take r.2.2

theorem mem_sliceOf {α : Type u} {SH : List (List α)} {r : ℕ × ℕ × ℕ} {x : α}
    (h : x ∈ sliceOf SH r) : ∃ S ∈ SH, x ∈ S := by
  unfold sliceOf at h
  have h1 := List.mem_of_mem_drop (List.mem_of_mem_take h)
  rw [List.getD_eq_getElem?_getD] at h1
  cases hS : SH[r.1]? with
  | none => rw [hS] at h1; simp at h1
  | some S => rw [hS] at h1; exact ⟨S, List.mem_of_getElem? hS, h1⟩

/-- Every entry of a concatenation of shard slices comes from some shard. -/
theorem mem_slices {α : Type u} {SH : List (List α)} {runs : List (ℕ × ℕ × ℕ)} {x : α}
    (h : x ∈ (runs.map (sliceOf SH)).flatten) : ∃ S ∈ SH, x ∈ S := by
  obtain ⟨l, hl, hx⟩ := List.mem_flatten.mp h
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hl
  exact mem_sliceOf hx

/-- `∀ S ∈ SH, ∀ x ∈ S, P x`, built shard by shard: empty list. -/
theorem shards_nil {α : Type u} {P : α → Prop} : ∀ S ∈ ([] : List (List α)), ∀ x ∈ S, P x := by
  intro S hS
  simp at hS

/-- `∀ S ∈ SH, ∀ x ∈ S, P x`, built shard by shard: cons. -/
theorem shards_cons {α : Type u} {P : α → Prop} {S0 : List α} {SH : List (List α)}
    (h0 : ∀ x ∈ S0, P x) (h : ∀ S ∈ SH, ∀ x ∈ S, P x) : ∀ S ∈ S0 :: SH, ∀ x ∈ S, P x := by
  intro S hS
  rcases List.mem_cons.mp hS with rfl | hS
  · exact h0
  · exact h S hS

end CKLaneG3

namespace CKLaneG3.S

open CKLaneD CKLaneG3

/-- Per-label binding of a DFS-ordered concatenation of shard slices to the archived (S) leaves:
one linear kernel walk of `sTree` (`tconsume`), no sorting. -/
theorem sLabel_family_of_slices {α : Type u} (n : ℕ) (SH : List (List α)) (f : α → List ℕ)
    (hSH : ∀ S ∈ SH, ∀ x ∈ S, SLeafOK (sBox (f x))) (runs : List (ℕ × ℕ × ℕ))
    (hc : (tconsume (fun l => l == n) sTree [] (((runs.map (sliceOf SH)).flatten).map f)).isSome = true) :
    ∀ q ∈ sTree.leaves, q.2 = n → SLeafOK (sBox q.1) :=
  sLabel_family_of_list n _ (fun p hp => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    obtain ⟨S, hS, hxS⟩ := mem_slices hx
    exact hSH S hS x hxS) hc

end CKLaneG3.S

end


