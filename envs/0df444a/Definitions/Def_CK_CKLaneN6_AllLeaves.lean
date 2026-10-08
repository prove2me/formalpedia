-- Prove2me | Definitions.Def_CK_CKLaneN6_AllLeaves
-- name    : CK_CKLaneN6_AllLeaves
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T21:36:33.618639+00:00
-- url     : https://prove2.me/theorems/b6ba3269-f7b8-4d25-813c-e8c0a3fc2a75
-- title:
--   Courtade–Kumar proof module `CKLaneN6.AllLeaves` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.AllLeaves` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.AllLeaves` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.AllLeaves (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/AllLeaves.lean)

import Definitions.Def_CK_CKLaneN6_TreeCover
import Definitions.Def_CK_CKLaneN6_Sub0
import Definitions.Def_CK_CKLaneN6_Sub1
import Definitions.Def_CK_CKLaneN6_Sub2
import Definitions.Def_CK_CKLaneN6_Sub3

-- ===== source module CKLaneN6.AllLeaves =====
section

/-!
# Lane N6: SMALL_RATIO Theorem 3 — every archived leaf, per-label families, the route row

63 coarse shards (7602 node certificates, 11215 kernel-checked cells) cover the 76,547 archived leaves of `archTree`:
`Asm.subOK_<P>` for each of the 64 depth-6 subtrees (`Asm.sub_<P>`: kernel decide against the shard leaf
lists), assembled through the top six levels by `PTree.forall_leavesR_node`.
`family_<label>` has the leaf-family shape `∀ q ∈ archTree.leaves, q.2 = code → LeafOK (feBox q.1)`;
`smallRatioT3NearRest : CKLaneN23.SmallRatioT3NearRest`.
-/

set_option autoImplicit false

namespace CKLaneN6

open CKLaneM05.FE8 CKLaneN6.ArchTree CKLaneN6.Asm

theorem PTree.forall_leavesR_node {P : List ℕ × ℕ → Prop} {ax : ℕ} {l r : PTree} {rpre : List ℕ}
    (hl : ∀ q ∈ l.leavesR (2 * ax :: rpre), P q) (hr : ∀ q ∈ r.leavesR ((2 * ax + 1) :: rpre), P q) :
    ∀ q ∈ (PTree.node ax l r).leavesR rpre, P q := by
  intro q hq
  simp only [PTree.leavesR, List.mem_append] at hq
  rcases hq with h | h
  · exact hl q h
  · exact hr q h

/-- Every archived Thm 3 leaf satisfies the row obligation on its exact box. -/
theorem all_leaves : ∀ q ∈ archTree.leaves, LeafOK (feBox q.1) :=
  (PTree.forall_leavesR_node (PTree.forall_leavesR_node (PTree.forall_leavesR_node (PTree.forall_leavesR_node (PTree.forall_leavesR_node (PTree.forall_leavesR_node subOK_024024 subOK_024025) (PTree.forall_leavesR_node subOK_024034 subOK_024035)) (PTree.forall_leavesR_node (PTree.forall_leavesR_node subOK_024124 subOK_024125) (PTree.forall_leavesR_node subOK_024134 subOK_024135))) (PTree.forall_leavesR_node (PTree.forall_leavesR_node (PTree.forall_leavesR_node subOK_025024 subOK_025025) (PTree.forall_leavesR_node subOK_025034 subOK_025035)) (PTree.forall_leavesR_node (PTree.forall_leavesR_node subOK_025124 subOK_025125) (PTree.forall_leavesR_node subOK_025134 subOK_025135)))) (PTree.forall_leavesR_node (PTree.forall_leavesR_node (PTree.forall_leavesR_node (PTree.forall_leavesR_node subOK_034024 subOK_034025) (PTree.forall_leavesR_node subOK_034034 subOK_034035)) (PTree.forall_leavesR_node (PTree.forall_leavesR_node subOK_034124 subOK_034125) (PTree.forall_leavesR_node subOK_034134 subOK_034135))) (PTree.forall_leavesR_node (PTree.forall_leavesR_node (PTree.forall_leavesR_node subOK_035024 subOK_035025) (PTree.forall_leavesR_node subOK_035034 subOK_035035)) (PTree.forall_leavesR_node (PTree.forall_leavesR_node subOK_035124 subOK_035125) (PTree.forall_leavesR_node subOK_035134 subOK_035135))))) (PTree.forall_leavesR_node (PTree.forall_leavesR_node (PTree.forall_leavesR_node (PTree.forall_leavesR_node (PTree.forall_leavesR_node subOK_124024 subOK_124025) (PTree.forall_leavesR_node subOK_124034 subOK_124035)) (PTree.forall_leavesR_node (PTree.forall_leavesR_node subOK_124124 subOK_124125) (PTree.forall_leavesR_node subOK_124134 subOK_124135))) (PTree.forall_leavesR_node (PTree.forall_leavesR_node (PTree.forall_leavesR_node subOK_125024 subOK_125025) (PTree.forall_leavesR_node subOK_125034 subOK_125035)) (PTree.forall_leavesR_node (PTree.forall_leavesR_node subOK_125124 subOK_125125) (PTree.forall_leavesR_node subOK_125134 subOK_125135)))) (PTree.forall_leavesR_node (PTree.forall_leavesR_node (PTree.forall_leavesR_node (PTree.forall_leavesR_node subOK_134024 subOK_134025) (PTree.forall_leavesR_node subOK_134034 subOK_134035)) (PTree.forall_leavesR_node (PTree.forall_leavesR_node subOK_134124 subOK_134125) (PTree.forall_leavesR_node subOK_134134 subOK_134135))) (PTree.forall_leavesR_node (PTree.forall_leavesR_node (PTree.forall_leavesR_node subOK_135024 subOK_135025) (PTree.forall_leavesR_node subOK_135034 subOK_135035)) (PTree.forall_leavesR_node (PTree.forall_leavesR_node subOK_135124 subOK_135125) (PTree.forall_leavesR_node subOK_135134 subOK_135135))))))

/-- Family theorem, archived label `outside` (code 0). -/
theorem family_outside : ∀ q ∈ archTree.leaves, q.2 = 0 → LeafOK (feBox q.1) :=
  fun q hq _ => all_leaves q hq

/-- Family theorem, archived label `prior_same_side` (code 1). -/
theorem family_prior_same_side : ∀ q ∈ archTree.leaves, q.2 = 1 → LeafOK (feBox q.1) :=
  fun q hq _ => all_leaves q hq

/-- Family theorem, archived label `central_small_ratio` (code 2). -/
theorem family_central_small_ratio : ∀ q ∈ archTree.leaves, q.2 = 2 → LeafOK (feBox q.1) :=
  fun q hq _ => all_leaves q hq

/-- Family theorem, archived label `cap` (code 3). -/
theorem family_cap : ∀ q ∈ archTree.leaves, q.2 = 3 → LeafOK (feBox q.1) :=
  fun q hq _ => all_leaves q hq

/-- Family theorem, archived label `phi_parent` (code 4). -/
theorem family_phi_parent : ∀ q ∈ archTree.leaves, q.2 = 4 → LeafOK (feBox q.1) :=
  fun q hq _ => all_leaves q hq

/-- Family theorem, archived label `phi_parent_log` (code 5). -/
theorem family_phi_parent_log : ∀ q ∈ archTree.leaves, q.2 = 5 → LeafOK (feBox q.1) :=
  fun q hq _ => all_leaves q hq

/-- Family theorem, archived label `sum_normalized` (code 6). -/
theorem family_sum_normalized : ∀ q ∈ archTree.leaves, q.2 = 6 → LeafOK (feBox q.1) :=
  fun q hq _ => all_leaves q hq

/-- Family theorem, archived label `endpoint_sum` (code 7). -/
theorem family_endpoint_sum : ∀ q ∈ archTree.leaves, q.2 = 7 → LeafOK (feBox q.1) :=
  fun q hq _ => all_leaves q hq

/-- Family theorem, archived label `logsum` (code 8). -/
theorem family_logsum : ∀ q ∈ archTree.leaves, q.2 = 8 → LeafOK (feBox q.1) :=
  fun q hq _ => all_leaves q hq

/-- Family theorem, archived label `logsum_quadratic` (code 9). -/
theorem family_logsum_quadratic : ∀ q ∈ archTree.leaves, q.2 = 9 → LeafOK (feBox q.1) :=
  fun q hq _ => all_leaves q hq

/-- Family theorem, archived label `logsum_quad_endpoints` (code 10). -/
theorem family_logsum_quad_endpoints : ∀ q ∈ archTree.leaves, q.2 = 10 → LeafOK (feBox q.1) :=
  fun q hq _ => all_leaves q hq

/-- Family theorem, archived label `shifted_logsum` (code 11). -/
theorem family_shifted_logsum : ∀ q ∈ archTree.leaves, q.2 = 11 → LeafOK (feBox q.1) :=
  fun q hq _ => all_leaves q hq

/-- Family theorem, archived label `endpoint_plane_endpoints` (code 12). -/
theorem family_endpoint_plane_endpoints : ∀ q ∈ archTree.leaves, q.2 = 12 → LeafOK (feBox q.1) :=
  fun q hq _ => all_leaves q hq

/-- Family theorem, archived label `endpoint_plane_taylor` (code 13). -/
theorem family_endpoint_plane_taylor : ∀ q ∈ archTree.leaves, q.2 = 13 → LeafOK (feBox q.1) :=
  fun q hq _ => all_leaves q hq

/-- **SMALL_RATIO Theorem 3, row 7 of `CKLaneN23.sameSideHalf_of_certificate_rows`.** -/
theorem smallRatioT3NearRest : CKLaneN23.SmallRatioT3NearRest :=
  row_of_all_leaves all_leaves

end CKLaneN6

end


