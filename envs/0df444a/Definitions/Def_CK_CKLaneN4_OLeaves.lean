-- Prove2me | Definitions.Def_CK_CKLaneN4_OLeaves
-- name    : CK_CKLaneN4_OLeaves
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T04:03:43.700004+00:00
-- url     : https://prove2.me/theorems/1276e3bd-a2ab-48b5-b061-203165a43ada
-- title:
--   Courtade–Kumar proof module `CKLaneN4.OLeaves` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.OLeaves` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.OLeaves` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.OLeaves (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/OLeaves.lean)

import Definitions.Def_CK_CKLaneN4_OLeafKernel
import Definitions.Def_CK_CKLaneN4_OLeavesLit
import Definitions.Def_CK_CKLaneN4_L4_S00
import Definitions.Def_CK_CKLaneN4_L4_S01
import Definitions.Def_CK_CKLaneN4_L4_S02
import Definitions.Def_CK_CKLaneN4_L4_S03
import Definitions.Def_CK_CKLaneN4_L4_S04
import Definitions.Def_CK_CKLaneN4_L4_S05
import Definitions.Def_CK_CKLaneN4_L4_S06
import Definitions.Def_CK_CKLaneN4_L4_S07
import Definitions.Def_CK_CKLaneG1_E25All

-- ===== source module CKLaneN4.OLeaves =====
section

/-!
# Lane N4: the (O) leaf families for archived labels 4, 7, 8, 9, 10 (OP_Compact-region form)

`LIT` (`CKLaneN4.OLeavesLit`, `lit_eq`): all archived (O) leaves with label 4, 7, 8, 9 or 10, in tree
order: 939 + 135 + 82 + 17 + 13 = 1186.

* label 4 (`global_eight_ratio`, 939): kernel-checked `checkL4` witnesses (shards `CKLaneN4.L4.S*`),
  bound path-by-path to `LIT` (`w4_paths`) — archived eight-ratio ∪ PARENT8 test on the full image;
* labels 7 / 8 / 9 / 10 (`global_parent8` 135, `global_low_entropy_025` 82, `global_parent16` 17,
  `global_parent_direct` 13): every
  leaf path occurs in Lane G1's `E ≤ 1/25` list (`le_cover`, linear merge check `subsetMerge`), whence
  `OP_LowEntropy25` (`oLeafOK_of_le25`).
-/

namespace CKLaneN4.OLeaves

open CKLaneD CKLaneD.OCompact CKLaneN4

set_option maxRecDepth 200000

/-- Linear merge check: every element of `L` occurs in `M` (matched in order). -/
def subsetMerge : List (List ℕ) → List (List ℕ) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x = y then subsetMerge xs ys else subsetMerge (x :: xs) ys

theorem subsetMerge_sound : ∀ (M L : List (List ℕ)), subsetMerge L M = true → ∀ x ∈ L, x ∈ M
  | [], [], _, x, hx => by simp at hx
  | [], _ :: _, h, _, _ => by simp [subsetMerge] at h
  | _ :: _, [], _, x, hx => by simp at hx
  | y :: ys, x :: xs, h, z, hz => by
    unfold subsetMerge at h
    split_ifs at h with hxy
    · have ih := subsetMerge_sound ys xs h
      rcases List.mem_cons.mp hz with hz | hz
      · subst hz; subst hxy; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih z hz)
    · have ih := subsetMerge_sound ys (x :: xs) h
      exact List.mem_cons_of_mem _ (ih z hz)

/-- The label-4 witnesses of all shards. -/
noncomputable def W4 : List (List ℕ × L4Witness) :=
  L4.S00.leaves ++ (L4.S01.leaves ++ (L4.S02.leaves ++ (L4.S03.leaves ++ (L4.S04.leaves ++ (L4.S05.leaves ++ (L4.S06.leaves ++ (L4.S07.leaves)))))))

theorem sem_append {L1 L2 : List (List ℕ × L4Witness)} (h1 : ∀ x ∈ L1, OLeafOK (uvtBox x.1))
    (h2 : ∀ x ∈ L2, OLeafOK (uvtBox x.1)) : ∀ x ∈ L1 ++ L2, OLeafOK (uvtBox x.1) :=
  fun x hx => (List.mem_append.mp hx).elim (h1 x) (h2 x)

theorem w4_sem : ∀ x ∈ W4, OLeafOK (uvtBox x.1) :=
  sem_append L4.S00.sem (sem_append L4.S01.sem (sem_append L4.S02.sem (sem_append L4.S03.sem (sem_append L4.S04.sem (sem_append L4.S05.sem (sem_append L4.S06.sem (L4.S07.sem)))))))

theorem w4_paths : (LIT.filter (fun x => x.2 = 4)).map Prod.fst = W4.map Prod.fst := by
  decide +kernel

theorem le_cover : subsetMerge
    ((LIT.filter (fun x => x.2 = 7 ∨ x.2 = 8 ∨ x.2 = 9 ∨ x.2 = 10)).map Prod.fst)
    (CKLaneG1.E25All.all.map Prod.fst) = true := by decide +kernel

theorem mem_LIT {q : List ℕ × ℕ} (hq : q ∈ ArchTree.archTree.leaves)
    (hl : q.2 = 4 ∨ q.2 = 7 ∨ q.2 = 8 ∨ q.2 = 9 ∨ q.2 = 10) : q ∈ LIT := by
  rw [← lit_eq]
  exact List.mem_filter.mpr ⟨hq, by simpa using hl⟩

theorem family_label4 : ∀ q ∈ ArchTree.archTree.leaves, q.2 = 4 → OLeafOK (uvtBox q.1) := by
  intro q hq hl
  have hL := mem_LIT hq (Or.inl hl)
  have hmem : q.1 ∈ (LIT.filter (fun x => x.2 = 4)).map Prod.fst :=
    List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨hL, by simpa using hl⟩, rfl⟩
  rw [w4_paths] at hmem
  obtain ⟨x, hx, hxq⟩ := List.mem_map.mp hmem
  rw [← hxq]
  exact w4_sem x hx

theorem family_le25 (q : List ℕ × ℕ) (hq : q ∈ ArchTree.archTree.leaves)
    (hl : q.2 = 7 ∨ q.2 = 8 ∨ q.2 = 9 ∨ q.2 = 10) : OLeafOK (uvtBox q.1) := by
  have hL := mem_LIT hq (Or.inr hl)
  have hmem : q.1 ∈ (LIT.filter (fun x => x.2 = 7 ∨ x.2 = 8 ∨ x.2 = 9 ∨ x.2 = 10)).map Prod.fst :=
    List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨hL, by simpa using hl⟩, rfl⟩
  obtain ⟨x, hx, hxq⟩ := List.mem_map.mp (subsetMerge_sound _ _ le_cover q.1 hmem)
  apply oLeafOK_of_le25
  rw [← hxq]
  exact CKLaneG1.E25All.all_le x hx

theorem family_label7 : ∀ q ∈ ArchTree.archTree.leaves, q.2 = 7 → OLeafOK (uvtBox q.1) :=
  fun q hq hl => family_le25 q hq (Or.inl hl)

theorem family_label8 : ∀ q ∈ ArchTree.archTree.leaves, q.2 = 8 → OLeafOK (uvtBox q.1) :=
  fun q hq hl => family_le25 q hq (Or.inr (Or.inl hl))

theorem family_label9 : ∀ q ∈ ArchTree.archTree.leaves, q.2 = 9 → OLeafOK (uvtBox q.1) :=
  fun q hq hl => family_le25 q hq (Or.inr (Or.inr (Or.inl hl)))

theorem family_label10 : ∀ q ∈ ArchTree.archTree.leaves, q.2 = 10 → OLeafOK (uvtBox q.1) :=
  fun q hq hl => family_le25 q hq (Or.inr (Or.inr (Or.inr hl)))

end CKLaneN4.OLeaves

end


