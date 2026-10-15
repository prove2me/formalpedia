-- Prove2me | Definitions.Def_OAI_Combinatorics_ParityLifts_Rerooting
-- name    : OAI_Combinatorics_ParityLifts_Rerooting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:22:51.735279+00:00
-- url     : https://prove2.me/theorems/9907cd54-7d18-43fd-843c-f50dff804fdf
-- title:
--   Adding a new root bag to a rooted test and forgetting root labels
-- statement:
--   This module changes which vertices of a rooted test serve as roots by placing a new root bag on top of its tree decomposition. Rooted tests are as in the rooted-test definitions: a finite vertex set $X_F$ with a symmetric relation $R_F$, root labels $\rho_F(j)$, and a rooted tree decomposition with bags of size at most $t$, child–parent intersections of size less than $t$, and root bag equal to the set of roots. For a graph $G$ on $V$ and a tuple $x$, $\hom_x(F,G)$ is the number of relation-preserving maps $X_F\to V$ sending $\rho_F(j)$ to $x_j$.
--
--   1. **Adding a root to a ranked tree.** A ranked tree on a node set $N$ is a rooted tree given by a root, a parent map, and a rank function that strictly decreases from every non-root node to its parent. Its extension $D^{+}$ has node set $N\sqcup\{\ast\}$, root $\ast$, the old root as the child of $\ast$, all other parents unchanged, and ranks increased by one ($\ast$ has rank $0$). The ancestor relation between old nodes is the same in $D$ and in $D^{+}$.
--
--   2. **Re-rooting.** Let $F$ be a rooted test with $r$ roots and width parameter $t$, let $\sigma:\{0,\dots,k-1\}\to\{0,\dots,r-1\}$, and assume $k<t$. The re-rooted test $F^{\sigma}$ has the same vertices and relation as $F$, the root labelling $\rho_F\circ\sigma$, and the decomposition on $D^{+}$ in which the new root $\ast$ carries the bag $\{\rho_F(\sigma(j)) : j<k\}$ and every old node keeps its bag. A kept root $\rho_F(\sigma(j))$ has the new root bag as its highest bag, and every other vertex keeps its highest bag; roots of $F$ that are not selected by $\sigma$ become ordinary vertices. The hypothesis $k<t$ guarantees that the new root bag has at most $t$ elements and meets the old root bag in fewer than $t$ elements.
--
--   3. **Forgetting one root.** Let $F$ have $k+1$ roots, let $i\in\{0,\dots,k\}$, and let $\sigma$ be the increasing embedding of $\{0,\dots,k-1\}$ into $\{0,\dots,k\}$ that skips $i$. For every graph $G$ on $V$ and $x\in V^k$, the maps of $F^{\sigma}$ over $x$ correspond bijectively to pairs $(y,f)$ with $y\in V$ and $f$ a map of $F$ over the tuple $x^{(i\leftarrow y)}=(x_0,\dots,x_{i-1},y,x_i,\dots,x_{k-1})$; the vertex $y$ is the image of the forgotten root $\rho_F(i)$. Hence, for finite $V$,
--   $$
--   \hom_x(F^{\sigma},G)=\sum_{y\in V}\hom_{x^{(i\leftarrow y)}}(F,G).
--   $$
--
--   Forgetting a root label therefore corresponds to summing a count function over one coordinate. This is how the span of rooted test counts is shown to be stable under summing out a coordinate, as long as the number of remaining roots is smaller than the width parameter.
--
--   **Formalization Note** The extended tree is `addRootTree D` on `Option N` (the new root is `none`); the re-rooted test is `reRootTest F ρ hk` with bags `reRootBag` and highest bags `reRootTop`, a kept root being one satisfying `keepRoot`. The bijection for forgetting a root is `reRootMapsEquiv`, where $\sigma$ is `i.succAbove` and $x^{(i\leftarrow y)}$ is `i.insertNth y x`. The private `ite_eq_left`/`ite_eq_right` lemmas are compatibility aliases.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/Rerooting.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/Rerooting.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueVertices

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace ParityWL

open scoped BigOperators

section AddRoot

open scoped Classical

variable {N : Type} (D : RankedTree N)

noncomputable def addRootTree : RankedTree (Option N) where
  root := none
  parent := fun n => match n with
    | none => none
    | some a => if a = D.root then none else some (D.parent a)
  rank := fun n => match n with
    | none => 0
    | some a => D.rank a + 1
  parent_lt := by
    intro n hn
    cases n with
    | none => exact (hn rfl).elim
    | some a =>
      dsimp only
      split_ifs with ha
      · simp only; omega
      · exact Nat.add_lt_add_right (D.parent_lt a ha) 1

lemma addRoot_map_ancestor {a b : N} (h : D.Ancestor a b) :
    (addRootTree D).Ancestor (some a) (some b) := by
  apply RankedTree.Ancestor.map D (addRootTree D) some _ h
  intro j hj
  apply RankedTree.Ancestor.step (by simp [addRootTree])
  simp only [addRootTree, ite_eq_right hj]
  exact .refl

lemma addRoot_ancestor_some {a : N} {n : Option N}
    (h : (addRootTree D).Ancestor (some a) n) :
    ∃ b, n = some b ∧ D.Ancestor a b := by
  induction h with
  | refl => exact ⟨a, rfl, .refl⟩
  | @step n hn h ih =>
    cases n with
    | none => exact (hn rfl).elim
    | some b =>
      obtain ⟨c, hc, hac⟩ := ih
      change (if b = D.root then none else some (D.parent b)) = some c at hc
      by_cases hb : b = D.root
      · rw [ite_eq_left hb] at hc
        cases hc
      · rw [ite_eq_right hb] at hc
        exact ⟨b, rfl, .step hb (by rwa [Option.some.inj hc])⟩

lemma addRoot_ancestor_iff {a b : N} :
    (addRootTree D).Ancestor (some a) (some b) ↔ D.Ancestor a b := by
  constructor
  · intro h
    obtain ⟨c, hc, hac⟩ := addRoot_ancestor_some D h
    rwa [Option.some.inj hc]
  · exact addRoot_map_ancestor D

end AddRoot

section ReRoot

open scoped Classical

variable {r k t : ℕ} (F : RootedTest r t) (ρ : Fin k → Fin r)

def keepRoot (a : F.Vertex) := ∃ j, F.roots (ρ j) = a

noncomputable def reRootBag : Option F.Node → Finset F.Vertex
  | none => Finset.univ.image (F.roots ∘ ρ)
  | some n => F.tree.bag n

noncomputable def reRootTop (a : F.Vertex) : Option F.Node :=
  if keepRoot F ρ a then none else some (F.tree.top a)

lemma keep_top {a : F.Vertex} (ha : keepRoot F ρ a) : F.tree.top a = F.tree.root := by
  apply RankedTree.ancestor_root_eq
  apply F.tree.top_ancestor
  rw [F.root_bag]
  obtain ⟨j, hj⟩ := ha
  exact Finset.mem_image.mpr ⟨ρ j, Finset.mem_univ _, hj⟩

lemma reRootTop_mem (a : F.Vertex) : a ∈ reRootBag F ρ (reRootTop F ρ a) := by
  by_cases ha : keepRoot F ρ a
  · simp only [reRootTop, ite_eq_left ha, reRootBag, Finset.mem_image, Finset.mem_univ,
      true_and, Function.comp_apply]
    exact ha
  · simpa only [reRootTop, ite_eq_right ha, reRootBag] using F.tree.top_mem a

lemma reRootTop_ancestor (a : F.Vertex) (n : Option F.Node)
    (han : a ∈ reRootBag F ρ n) :
    (addRootTree F.tree.toRankedTree).Ancestor (reRootTop F ρ a) n := by
  by_cases ha : keepRoot F ρ a
  · rw [reRootTop, ite_eq_left ha]
    exact (addRootTree F.tree.toRankedTree).root_ancestor n
  · rw [reRootTop, ite_eq_right ha]
    cases n with
    | none => exact (ha (by simpa only [keepRoot, reRootBag, Finset.mem_image,
        Finset.mem_univ, true_and, Function.comp_apply] using han)).elim
    | some n => exact addRoot_map_ancestor _ (F.tree.top_ancestor a n han)

lemma reRootInterval_mem (a : F.Vertex) (n l : Option F.Node)
    (hn : (addRootTree F.tree.toRankedTree).Ancestor (reRootTop F ρ a) n)
    (hnl : (addRootTree F.tree.toRankedTree).Ancestor n l) (ha : a ∈ reRootBag F ρ l) :
    a ∈ reRootBag F ρ n := by
  cases n with
  | none =>
    have he := RankedTree.ancestor_root_eq (addRootTree F.tree.toRankedTree) hn
    have hk : keepRoot F ρ a := by
      by_contra hk
      rw [reRootTop, ite_eq_right hk] at he
      cases he
    simpa only [keepRoot, reRootBag, Finset.mem_image, Finset.mem_univ,
      true_and, Function.comp_apply] using hk
  | some n =>
    obtain ⟨l, rfl, hnl'⟩ := addRoot_ancestor_some _ hnl
    apply F.tree.interval_mem a n l _ hnl' ha
    by_cases hk : keepRoot F ρ a
    · rw [keep_top F ρ hk]
      exact F.tree.toRankedTree.root_ancestor n
    · rw [reRootTop, ite_eq_right hk] at hn
      exact (addRoot_ancestor_iff _).mp hn

noncomputable def reRootTest (hk : k < t) : RootedTest k t where
  Vertex := F.Vertex
  vertexFintype := F.vertexFintype
  relation := F.relation
  symmetric := F.symmetric
  roots := F.roots ∘ ρ
  Node := Option F.Node
  nodeFintype := inferInstance
  tree :=
    { toRankedTree := addRootTree F.tree.toRankedTree
      bag := reRootBag F ρ
      top := reRootTop F ρ
      top_mem := reRootTop_mem F ρ
      top_ancestor := reRootTop_ancestor F ρ
      interval_mem := reRootInterval_mem F ρ
      edge_cover := by
        intro a b hab
        obtain ⟨n, han, hbn⟩ := F.tree.edge_cover a b hab
        exact ⟨some n, han, hbn⟩
      width := by
        intro n
        cases n with
        | none =>
          exact le_trans Finset.card_image_le
            (by simpa only [Finset.card_univ, Fintype.card_fin] using hk.le)
        | some n => exact F.tree.width n
      intersection := by
        intro n hn
        cases n with
        | none => exact (hn rfl).elim
        | some n =>
          change (F.tree.bag n ∩ reRootBag F ρ
            (if n = F.tree.root then none else some (F.tree.parent n))).card < t
          by_cases he : n = F.tree.root
          · rw [ite_eq_left he]
            exact lt_of_le_of_lt ((Finset.card_le_card Finset.inter_subset_right).trans
              Finset.card_image_le) (by simpa using hk)
          · rw [ite_eq_right he]
            exact F.tree.intersection n he }
  root_bag := rfl

end ReRoot

section ForgetCount

open scoped Classical

variable {k t : ℕ} (F : RootedTest (k + 1) t) (i : Fin (k + 1)) (hk : k < t)
variable {V : Type} (G : SimpleGraph V) (x : Fin k → V)

noncomputable def reRootMapsEquiv :
    (reRootTest F i.succAbove hk).Maps G x ≃ ((y : V) × F.Maps G (i.insertNth y x)) where
  toFun f := ⟨f.1.1 (F.roots i), ⟨f.1, by
    intro j
    refine Fin.succAboveCases i ?_ (fun l => ?_) j
    · simp only [Fin.insertNth_apply_same]
    · rw [Fin.insertNth_apply_succAbove]
      exact f.2 l⟩⟩
  invFun f := ⟨f.2.1, by
    intro j
    change f.2.1.1 (F.roots (i.succAbove j)) = x j
    simpa only [Fin.insertNth_apply_succAbove] using f.2.2 (i.succAbove j)⟩
  left_inv _ := rfl
  right_inv f := by
    rcases f with ⟨y, f, hf⟩
    have hy : f.1 (F.roots i) = y := by
      simpa only [Fin.insertNth_apply_same] using hf i
    subst y
    rfl

end ForgetCount

end ParityWL

end OAI


