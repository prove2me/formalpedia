-- Prove2me | Definitions.Def_OAI_Combinatorics_ParityLifts_GlueTrees
-- name    : OAI_Combinatorics_ParityLifts_GlueTrees
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:17:45.99539+00:00
-- url     : https://prove2.me/theorems/187826c2-a8b4-4fcd-bd29-5cef922e47b9
-- title:
--   Gluing the decomposition trees of rooted tests at a common root
-- statement:
--   Let $(F_i)_{i\in I}$ be a family of rooted tests with bag bound $t$, where $F_i$ has $r_i$ roots, and let $\mathcal T_i$ be the ranked tree of $F_i$, with root $\rho_i$, parent map $\mathrm{par}_i$ and rank $\mathrm{rk}_i$.
--
--   1. **Glued nodes.** The node set is
--   $$
--   \{\star\}\ \sqcup\ \bigsqcup_{i\in I}\bigl(N(\mathcal T_i)\setminus\{\rho_i\}\bigr),
--   $$
--   a new root $\star$ together with all non-root nodes of all the trees. The map $\iota_i$ sends a node $n$ of $\mathcal T_i$ to $\star$ if $n=\rho_i$, and to the node $(i,n)$ otherwise.
--   2. **Glued tree.** Its parent map is $\mathrm{par}(\star)=\star$ and $\mathrm{par}(i,n)=\iota_i(\mathrm{par}_i(n))$, and its ranks are $\mathrm{rk}(\star)=0$ and $\mathrm{rk}(i,n)=\mathrm{rk}_i(n)+1$. This is a ranked tree with root $\star$; in effect, all the roots $\rho_i$ are identified into the single node $\star$.
--
--   The following facts are proved alongside:
--   - $\iota_i(\rho_i)=\star$, and $\iota_i(n)=(i,n)$ for $n\ne\rho_i$;
--   - $\iota_i$ preserves ancestry: $a\preceq b$ in $\mathcal T_i$ implies $\iota_i(a)\preceq\iota_i(b)$ in the glued tree;
--   - descendants of a non-root node stay in its tree: if $(i,a)\preceq n$, then $n=(i,b)$ for some $b$ with $a\preceq b$ in $\mathcal T_i$;
--   - in any ranked tree, the only ancestor of the root is the root itself;
--   - in a rooted test, every root vertex has its highest occurrence at the root node, and hence lies in the bag of every ancestor of any node whose bag contains it.
--
--   This is the tree on which rooted tests are later glued along their roots: the shared interface becomes the bag of the new root $\star$, and the last fact keeps the occurrence sets of merged root vertices connected. In this way products and replacement sums of rooted counts are again rooted counts of sources with bags of size at most $t$.
--
--   **Formalization Note** The node type is `GlueNode F`, an `Option` of a sigma type of non-root nodes with `none` as the new root; the maps are `glueNodeMap`, `glueNodeParent`, `glueNodeRank`, and the tree is `glueTree F`. The listed facts are `glueNodeMap_root`, `glueNodeMap_nonroot`, `glueTree_map_ancestor`, `glueTree_ancestor_from_some`, `RankedTree.ancestor_root_eq`, `rooted_top_eq_root` and `rooted_mem_ancestor`. The private lemmas `dite_eq_left` and `dite_eq_right` are compatibility shims.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/GlueTrees.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/GlueTrees.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ParityLifts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BagTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_TagSizes
import Definitions.Def_OAI_Combinatorics_ParityLifts_Detection
import Definitions.Def_OAI_Combinatorics_ParityLifts_RankedTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_RootedTests

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

namespace ParityWL

open scoped BigOperators

section GlueTrees

open scoped Classical

variable {I : Type} {r : I → ℕ} {t : ℕ} (F : (i : I) → RootedTest (r i) t)

abbrev GlueNode := Option ((i : I) × {n : (F i).Node // n ≠ (F i).tree.root})

noncomputable def glueNodeMap (i : I) (n : (F i).Node) : GlueNode F :=
  if h : n = (F i).tree.root then none else some ⟨i, ⟨n, h⟩⟩

noncomputable def glueNodeParent : GlueNode F → GlueNode F
  | none => none
  | some ⟨i, n⟩ => glueNodeMap F i ((F i).tree.parent n)

noncomputable def glueNodeRank : GlueNode F → ℕ
  | none => 0
  | some ⟨i, n⟩ => (F i).tree.rank n + 1

noncomputable def glueTree : RankedTree (GlueNode F) where
  root := none
  parent := glueNodeParent F
  rank := glueNodeRank F
  parent_lt := by
    intro n hn
    cases n with
    | none => exact (hn rfl).elim
    | some q =>
      rcases q with ⟨i, n⟩
      simp only [glueNodeParent, glueNodeMap]
      split_ifs
      · simp only [glueNodeRank]; omega
      · simpa only [glueNodeRank, Nat.add_lt_add_iff_right] using
          (F i).tree.parent_lt n.1 n.2

lemma glueNodeMap_root (i : I) : glueNodeMap F i (F i).tree.root = none := by
  simp [glueNodeMap]

lemma glueNodeMap_nonroot (i : I) (n : (F i).Node) (hn : n ≠ (F i).tree.root) :
    glueNodeMap F i n = some ⟨i, ⟨n, hn⟩⟩ := by
  simp only [glueNodeMap, dite_eq_right hn]

lemma glueTree_map_ancestor (i : I) {a b : (F i).Node}
    (h : (F i).tree.toRankedTree.Ancestor a b) :
    (glueTree F).Ancestor (glueNodeMap F i a) (glueNodeMap F i b) := by
  apply RankedTree.Ancestor.map _ (glueTree F) (glueNodeMap F i) _ h
  intro j hj
  rw [glueNodeMap_nonroot F i j hj]
  apply RankedTree.Ancestor.step (by simp [glueTree])
  exact .refl

lemma glueTree_ancestor_from_some {i : I}
    {a : {n : (F i).Node // n ≠ (F i).tree.root}} {n : GlueNode F}
    (h : (glueTree F).Ancestor (some ⟨i, a⟩) n) :
    ∃ b : {n : (F i).Node // n ≠ (F i).tree.root}, n = some ⟨i, b⟩ ∧
      (F i).tree.toRankedTree.Ancestor a.1 b.1 := by
  induction h with
  | refl => exact ⟨a, rfl, .refl⟩
  | @step n hn h ih =>
    cases n with
    | none => exact (hn rfl).elim
    | some q =>
      rcases q with ⟨j, b⟩
      obtain ⟨c, hc, hac⟩ := ih
      change glueNodeMap F j ((F j).tree.parent b.1) = some ⟨i, c⟩ at hc
      by_cases hp : (F j).tree.parent b.1 = (F j).tree.root
      · simp only [glueNodeMap, dite_eq_left hp] at hc
        cases hc
      · rw [glueNodeMap_nonroot F j _ hp] at hc
        have hji : j = i := congrArg Sigma.fst (Option.some.inj hc)
        subst j
        have hb : (F i).tree.parent b.1 = c.1 := by
          have he : (⟨(F i).tree.parent b.1, hp⟩ : {n // n ≠ (F i).tree.root}) = c := by
            simpa only [Option.some.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] using hc
          exact congrArg Subtype.val he
        exact ⟨b, rfl, .step b.2 (by rwa [hb])⟩

lemma RankedTree.ancestor_root_eq {N : Type} (D : RankedTree N) {i : N}
    (h : D.Ancestor i D.root) : i = D.root := by
  rcases h.cases' D with he | ⟨hne, _⟩
  · exact he
  · exact (hne rfl).elim

lemma rooted_top_eq_root (i : I) {a : (F i).Vertex}
    (ha : ∃ j, (F i).roots j = a) : (F i).tree.top a = (F i).tree.root := by
  apply RankedTree.ancestor_root_eq
  apply (F i).tree.top_ancestor
  rw [(F i).root_bag]
  simpa only [Finset.mem_image, Finset.mem_univ, true_and] using ha

lemma rooted_mem_ancestor (i : I) {a : (F i).Vertex} {n m : (F i).Node}
    (ha : ∃ j, (F i).roots j = a) (hn : (F i).tree.toRankedTree.Ancestor n m)
    (ham : a ∈ (F i).tree.bag m) : a ∈ (F i).tree.bag n := by
  apply (F i).tree.interval_mem a n m _ hn ham
  rw [rooted_top_eq_root F i ha]
  exact (F i).tree.toRankedTree.root_ancestor n

end GlueTrees

end ParityWL

end OAI


