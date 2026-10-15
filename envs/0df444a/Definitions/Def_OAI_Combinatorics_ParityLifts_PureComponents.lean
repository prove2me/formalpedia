-- Prove2me | Definitions.Def_OAI_Combinatorics_ParityLifts_PureComponents
-- name    : OAI_Combinatorics_ParityLifts_PureComponents
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:30:26.339682+00:00
-- url     : https://prove2.me/theorems/bbee485b-a6b3-4869-9f15-f24276137a6d
-- title:
--   Root-preserving maps into a disjoint union split along a two-colouring of components
-- statement:
--   Let $F$ be a rooted test with $k$ roots and width parameter $t$: a finite vertex set $X_F$ with a symmetric relation $R_F$, root labels $\rho_F(0),\dots,\rho_F(k-1)$, and a rooted tree decomposition with bags of size at most $t$ and child–parent intersections of size less than $t$. Let $G$ and $H$ be simple graphs on sets $V$ and $W$, and write $G\sqcup H$ for their disjoint union on $V\sqcup W$, whose edges are the edges of $G$ and the edges of $H$.
--
--   1. **Induced decomposition.** For a tree decomposition $D$ of a relation $R$ on a set $X$ (bags of size at most $t$, child–parent intersections of size less than $t$) and a predicate $P$ on $X$, the induced decomposition of the restriction of $R$ to $\{p\in X:P(p)\}$ has the same tree and bags $B_n\cap\{p\in X:P(p)\}$; it satisfies the same width bounds.
--
--   2. **Pure-left maps.** These are the maps $f:X_F\to V\sqcup W$ with $f(p)f(q)\in E(G\sqcup H)$ whenever $p\,R_F\,q$, that send every root $\rho_F(j)$ into $V$.
--
--   3. **Component masks.** A component mask is a function $s:X_F\to\{\mathrm{true},\mathrm{false}\}$ with $s(p)=s(q)$ whenever $p\,R_F\,q$ (so $s$ is constant on connected components of $R_F$) and $s(\rho_F(j))=\mathrm{true}$ for every root. It splits $X_F$ into $X^{+}_s=s^{-1}(\mathrm{true})$ and $X^{-}_s=s^{-1}(\mathrm{false})$.
--
--   4. **Component maps.** For a mask $s$, a component map is a pair $(g,h)$ of maps $g:X^{+}_s\to V$ and $h:X^{-}_s\to W$ such that $g$ maps related pairs in $X^{+}_s$ to edges of $G$ and $h$ maps related pairs in $X^{-}_s$ to edges of $H$.
--
--   5. **Assembly bijection.** Sending $(s,(g,h))$ to the map that equals $g$ on $X^{+}_s$ and $h$ on $X^{-}_s$ is a bijection
--   $$
--   \bigsqcup_{s\text{ a component mask}}\{\text{component maps for }s\}\ \longrightarrow\ \{\text{pure-left maps of }F\text{ into }G\sqcup H\},
--   $$
--   whose inverse sends a pure-left map $f$ to the mask $s(p)=[f(p)\in V]$ together with the two restrictions of $f$.
--
--   Since no edge of $G\sqcup H$ joins $V$ to $W$, a relation-preserving map sends each connected component of the test entirely into one side, and components containing a root are forced into $G$; the bijection makes this precise. In the parity reduction it expresses counts of pure tuples in a disjoint union as sums of products of counts in the two graphs, each for a sub-test that still has a decomposition of the same width, which is how the pure version of Weisfeiler–Leman equivalence is handled.
--
--   **Formalization Note** The induced decomposition is `RankedBagTree.induce D P` (bags `(D.bag n).subtype P`). The other objects are `PureLeftMaps F G H` (relation maps into `G.sum H` whose root values satisfy `isLeft`), `ComponentMask F`, `MaskLeft`/`MaskRight`, `ComponentMaps F G H s`, the assembly `assemblePure` and the equivalence `componentEquiv`. The private `dite` lemmas are compatibility aliases.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/PureComponents.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/PureComponents.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_ParityLifts_Rerooting
import Definitions.Def_OAI_Combinatorics_ParityLifts_TestAlgebra
import Definitions.Def_OAI_Combinatorics_ParityLifts_Interpolation
import Definitions.Def_OAI_Combinatorics_ParityLifts_ColorSpan

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

namespace ParityWL

open scoped BigOperators

section InducedBagTree

open scoped Classical

variable {A N : Type} {R : A → A → Prop} {t : ℕ}

noncomputable def RankedBagTree.induce (D : RankedBagTree (N := N) R t) (P : A → Prop) :
    RankedBagTree (N := N) (fun a b : Subtype P => R a.1 b.1) t where
  toRankedTree := D.toRankedTree
  bag n := (D.bag n).subtype P
  top a := D.top a.1
  top_mem a := Finset.mem_subtype.mpr (D.top_mem a.1)
  top_ancestor a n ha := D.top_ancestor a.1 n (Finset.mem_subtype.mp ha)
  interval_mem a n l hn hnl ha :=
    Finset.mem_subtype.mpr (D.interval_mem a.1 n l hn hnl (Finset.mem_subtype.mp ha))
  edge_cover a b hab := by
    obtain ⟨n, han, hbn⟩ := D.edge_cover a.1 b.1 hab
    exact ⟨n, Finset.mem_subtype.mpr han, Finset.mem_subtype.mpr hbn⟩
  width n := by
    rw [Finset.card_subtype]
    exact (Finset.card_filter_le _ _).trans (D.width n)
  intersection n hn := by
    let : DecidableEq (Subtype P) := Classical.decEq _
    have he : (D.bag n).subtype P ∩ (D.bag (D.parent n)).subtype P =
        (D.bag n ∩ D.bag (D.parent n)).subtype P := by
      ext a
      simp only [Finset.mem_inter, Finset.mem_subtype]
    rw [he, Finset.card_subtype]
    exact lt_of_le_of_lt (Finset.card_filter_le _ _) (D.intersection n hn)

end InducedBagTree

section PureComponents

open scoped Classical

variable {k t : ℕ} (F : RootedTest k t)
variable {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W)

noncomputable def PureLeftMaps :=
  {f : RelationMaps F.relation (G.sum H) // ∀ i, (f.1 (F.roots i)).isLeft}

noncomputable instance pureLeftMapsFintype [Fintype V] [Fintype W] : Fintype (PureLeftMaps F G H) := by
  unfold PureLeftMaps
  infer_instance

def ComponentMask := {s : F.Vertex → Bool //
  (∀ a b, F.relation a b → s a = s b) ∧ ∀ i, s (F.roots i) = true}

noncomputable instance componentMaskFintype : Fintype (ComponentMask F) := by
  unfold ComponentMask
  infer_instance

abbrev MaskLeft (s : ComponentMask F) := {a : F.Vertex // s.1 a = true}
abbrev MaskRight (s : ComponentMask F) := {a : F.Vertex // s.1 a = false}

noncomputable def ComponentMaps (s : ComponentMask F) :=
  RelationMaps (fun a b : MaskLeft F s => F.relation a.1 b.1) G ×
  RelationMaps (fun a b : MaskRight F s => F.relation a.1 b.1) H

noncomputable instance componentMapsFintype [Fintype V] [Fintype W] (s : ComponentMask F) :
    Fintype (ComponentMaps F G H s) := by
  unfold ComponentMaps
  infer_instance

noncomputable def assembleFunction (s : ComponentMask F) (f : ComponentMaps F G H s)
    (a : F.Vertex) : V ⊕ W :=
  if h : s.1 a = true then .inl (f.1.1 ⟨a, h⟩)
  else .inr (f.2.1 ⟨a, Bool.eq_false_iff.mpr h⟩)

lemma assembleFunction_left (s : ComponentMask F) (f : ComponentMaps F G H s)
    (a : MaskLeft F s) : assembleFunction F G H s f a.1 = .inl (f.1.1 a) := by
  simp only [assembleFunction, dite_eq_left a.2]

lemma assembleFunction_right (s : ComponentMask F) (f : ComponentMaps F G H s)
    (a : MaskRight F s) : assembleFunction F G H s f a.1 = .inr (f.2.1 a) := by
  have ha : s.1 a.1 ≠ true := by rw [a.2]; decide
  simp only [assembleFunction, dite_eq_right ha]

lemma assembleFunction_isLeft (s : ComponentMask F) (f : ComponentMaps F G H s)
    (a : F.Vertex) : (assembleFunction F G H s f a).isLeft = s.1 a := by
  by_cases h : s.1 a = true
  · rw [assembleFunction_left F G H s f ⟨a, h⟩]
    exact h.symm
  · rw [assembleFunction_right F G H s f ⟨a, Bool.eq_false_iff.mpr h⟩]
    exact (Bool.eq_false_iff.mpr h).symm

noncomputable def assemblePure (f : (s : ComponentMask F) × ComponentMaps F G H s) :
    PureLeftMaps F G H := ⟨⟨assembleFunction F G H f.1 f.2, by
      intro a b hab
      have he := f.1.2.1 a b hab
      by_cases ha : f.1.1 a = true
      · have hb : f.1.1 b = true := he.symm.trans ha
        rw [assembleFunction_left F G H f.1 f.2 ⟨a, ha⟩,
          assembleFunction_left F G H f.1 f.2 ⟨b, hb⟩]
        exact f.2.1.2 ⟨a, ha⟩ ⟨b, hb⟩ hab
      · have ha' : f.1.1 a = false := Bool.eq_false_iff.mpr ha
        have hb : f.1.1 b = false := he.symm.trans ha'
        rw [assembleFunction_right F G H f.1 f.2 ⟨a, ha'⟩,
          assembleFunction_right F G H f.1 f.2 ⟨b, hb⟩]
        exact f.2.2.2 ⟨a, ha'⟩ ⟨b, hb⟩ hab⟩,
      fun i => by rw [assembleFunction_isLeft]; exact f.1.2.2 i⟩

lemma assemblePure_injective : Function.Injective (assemblePure F G H) := by
  rintro ⟨s, f⟩ ⟨s', f'⟩ he
  have hefun (a : F.Vertex) : assembleFunction F G H s f a = assembleFunction F G H s' f' a :=
    congrFun (congrArg (fun p => p.1.1) he) a
  have hs : s = s' := by
    apply Subtype.ext
    funext a
    rw [← assembleFunction_isLeft F G H s f a, ← assembleFunction_isLeft F G H s' f' a, hefun a]
  subst s'
  apply congrArg (Sigma.mk s)
  apply Prod.ext
  · apply Subtype.ext
    funext a
    apply Sum.inl_injective
    rw [← assembleFunction_left F G H s f a, ← assembleFunction_left F G H s f' a]
    exact hefun a.1
  · apply Subtype.ext
    funext a
    apply Sum.inr_injective
    rw [← assembleFunction_right F G H s f a, ← assembleFunction_right F G H s f' a]
    exact hefun a.1

lemma sum_adj_same_side {a b : V ⊕ W} (h : (G.sum H).Adj a b) : a.isLeft = b.isLeft := by
  cases a <;> cases b <;> simp_all only [SimpleGraph.sum_adj, Sum.isLeft_inl, Sum.isLeft_inr]

noncomputable def mapMask (f : PureLeftMaps F G H) : ComponentMask F :=
  ⟨fun a => (f.1.1 a).isLeft,
    (fun a b hab => sum_adj_same_side G H (f.1.2 a b hab)), f.2⟩

noncomputable def mapComponents (f : PureLeftMaps F G H) : ComponentMaps F G H (mapMask F G H f) :=
  (⟨fun a => (f.1.1 a.1).getLeft a.2, by
    intro a b hab
    have he := f.1.2 a.1 b.1 hab
    rw [← Sum.inl_getLeft (f.1.1 a.1) a.2, ← Sum.inl_getLeft (f.1.1 b.1) b.2] at he
    exact he⟩,
  ⟨fun a => (f.1.1 a.1).getRight (Sum.isLeft_eq_false.mp a.2), by
    intro a b hab
    have he := f.1.2 a.1 b.1 hab
    rw [← Sum.inr_getRight (f.1.1 a.1) (Sum.isLeft_eq_false.mp a.2),
      ← Sum.inr_getRight (f.1.1 b.1) (Sum.isLeft_eq_false.mp b.2)] at he
    exact he⟩)

lemma assemble_mapComponents (f : PureLeftMaps F G H) :
    assemblePure F G H ⟨mapMask F G H f, mapComponents F G H f⟩ = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext a
  change assembleFunction F G H (mapMask F G H f) (mapComponents F G H f) a = f.1.1 a
  by_cases h : (f.1.1 a).isLeft = true
  · rw [assembleFunction_left F G H (mapMask F G H f) (mapComponents F G H f) ⟨a, h⟩]
    exact Sum.inl_getLeft _ _
  · rw [assembleFunction_right F G H (mapMask F G H f) (mapComponents F G H f)
      ⟨a, Bool.eq_false_iff.mpr h⟩]
    exact Sum.inr_getRight _ _

noncomputable def componentEquiv :
    ((s : ComponentMask F) × ComponentMaps F G H s) ≃ PureLeftMaps F G H :=
  Equiv.ofBijective (assemblePure F G H) ⟨assemblePure_injective F G H,
    fun f => ⟨⟨mapMask F G H f, mapComponents F G H f⟩, assemble_mapComponents F G H f⟩⟩

end PureComponents

end ParityWL

end OAI


