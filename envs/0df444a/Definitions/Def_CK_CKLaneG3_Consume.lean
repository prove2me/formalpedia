-- Prove2me | Definitions.Def_CK_CKLaneG3_Consume
-- name    : CK_CKLaneG3_Consume
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T07:03:51.983981+00:00
-- url     : https://prove2.me/theorems/ebae3d16-53f0-4a91-b0b0-202a77b4b88f
-- title:
--   Courtade–Kumar proof module `CKLaneG3.Consume` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.Consume` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.Consume` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.Consume (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/Consume.lean)

import Definitions.Def_CK_CKLaneG3_Families

-- ===== source module CKLaneG3.Consume =====
section

/-!
# Lane G3 kernel v2: linear-time DFS consumer for leaf-family coverage checks

`tconsume good T rpre L` walks the subtree `T` (reversed path prefix `rpre`) in DFS order without
building leaf lists; at every `good` leaf it searches the leaf's path in the remaining certified list
`L` (`lfind`, which may skip unrelated entries) and continues with the suffix after it.
`leafFacts_of_consume`: if the walk succeeds, every `good` leaf path occurs in `L`, hence the leaf
family over the subtree follows from `∀ p ∈ L, RegionOn P (uvtBox p)`.
(The list-based check `leafFacts_of_sublist` enumerates `leavesR` with nested appends; measured
68.4 s kernel time on the full archived tree, versus 0.455 s for a label-only walk.)
-/

namespace CKLaneG3

open CKLaneD GeneralCK

/-- Search `p` in `L`; return the suffix after its first occurrence. -/
def lfind (p : List ℕ) : List (List ℕ) → Option (List (List ℕ))
  | [] => none
  | x :: xs => if x = p then some xs else lfind p xs

theorem lfind_spec {p : List ℕ} : ∀ {L L' : List (List ℕ)}, lfind p L = some L' →
    p ∈ L ∧ ∀ y ∈ L', y ∈ L
  | [], L', h => by simp [lfind] at h
  | x :: xs, L', h => by
      unfold lfind at h
      by_cases hx : x = p
      · rw [if_pos hx] at h
        cases h
        subst hx
        exact ⟨List.mem_cons_self .., fun y hy => List.mem_cons_of_mem _ hy⟩
      · rw [if_neg hx] at h
        obtain ⟨h1, h2⟩ := lfind_spec h
        exact ⟨List.mem_cons_of_mem _ h1, fun y hy => List.mem_cons_of_mem _ (h2 y hy)⟩

/-- DFS walk of `T` consuming the certified path list `L`. -/
def tconsume (good : ℕ → Bool) : PTree → List ℕ → List (List ℕ) → Option (List (List ℕ))
  | .leaf l, rpre, L => if good l then lfind rpre.reverse L else some L
  | .node ax l r, rpre, L =>
      (tconsume good l (2 * ax :: rpre) L).bind (tconsume good r ((2 * ax + 1) :: rpre))

theorem tconsume_spec {good : ℕ → Bool} : ∀ (T : PTree) (rpre : List ℕ) {L L' : List (List ℕ)},
    tconsume good T rpre L = some L' →
      (∀ q ∈ T.leavesR rpre, good q.2 = true → q.1 ∈ L) ∧ (∀ y ∈ L', y ∈ L)
  | .leaf l, rpre, L, L', h => by
      unfold tconsume at h
      by_cases hg : good l = true
      · rw [if_pos hg] at h
        obtain ⟨h1, h2⟩ := lfind_spec h
        refine ⟨fun q hq _ => ?_, h2⟩
        simp only [PTree.leavesR, List.mem_singleton] at hq
        subst hq
        exact h1
      · rw [if_neg hg] at h
        cases h
        refine ⟨fun q hq hq' => ?_, fun y hy => hy⟩
        simp only [PTree.leavesR, List.mem_singleton] at hq
        subst hq
        exact absurd hq' hg
  | .node ax l r, rpre, L, L', h => by
      unfold tconsume at h
      cases h1 : tconsume good l (2 * ax :: rpre) L with
      | none =>
          rw [h1] at h
          cases h
      | some L1 =>
          rw [h1] at h
          change tconsume good r ((2 * ax + 1) :: rpre) L1 = some L' at h
          obtain ⟨a1, b1⟩ := tconsume_spec l _ h1
          obtain ⟨a2, b2⟩ := tconsume_spec r _ h
          refine ⟨fun q hq hg => ?_, fun y hy => b1 y (b2 y hy)⟩
          simp only [PTree.leavesR, List.mem_append] at hq
          rcases hq with hq | hq
          · exact a1 q hq hg
          · exact b1 _ (a2 q hq hg)

/-- Level-1 aggregation with the linear-time consumer. -/
theorem leafFacts_of_consume {P : ∀ k : ℕ, InteriorLaw (Fin k) → Prop} {good : ℕ → Bool}
    (T : PTree) (rpre : List ℕ) (L : List (List ℕ)) (hL : ∀ p ∈ L, RegionOn P (uvtBox p))
    (hc : (tconsume good T rpre L).isSome = true) : LeafFacts P good T rpre := by
  intro q hq hg
  obtain ⟨L', hL'⟩ := Option.isSome_iff_exists.mp hc
  exact hL _ ((tconsume_spec T rpre hL').1 q hq hg)

/-- Per-label binding (coordinator shape, BRIEF §7) of a DFS-ordered certified path list to the
leaves of a tree, by one linear kernel walk (independent of the box semantics `Q`). -/
theorem label_family_of_consume {Q : List ℕ → Prop} (T : PTree) (n : ℕ) (L : List (List ℕ))
    (hL : ∀ p ∈ L, Q p) (hc : (tconsume (fun l => l == n) T [] L).isSome = true) :
    ∀ q ∈ T.leaves, q.2 = n → Q q.1 := by
  intro q hq hn
  obtain ⟨L', hL'⟩ := Option.isSome_iff_exists.mp hc
  exact hL _ ((tconsume_spec T [] hL').1 q hq (by simp [hn]))

end CKLaneG3

end


