-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PreorderIndex
-- name    : OAI_MeasureTheory_DyadicAvoidance_PreorderIndex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:54:34.541598+00:00
-- url     : https://prove2.me/theorems/2272b1bd-29c7-407f-b0e7-2dc716c588c0
-- title:
--   The arithmetic preorder rank equals the position in the listed edge preorder
-- statement:
--   This file identifies the arithmetic preorder rank of a tree node with its actual position in an explicitly listed depth-first enumeration of the tree edges, and records two general facts about positions in lists. For a finite list $L$ and an element $x$, let $\operatorname{idx}_L(x)$ be the zero-based position of the first occurrence of $x$ in $L$, with the convention $\operatorname{idx}_L(x)=|L|$ when $x$ does not occur in $L$.
--
--   Fix $K\in\mathbb{N}$. Nodes of the complete ordered $K$-ary tree are words $p=(p_1,\dots,p_m)$ over the labels $\{0,\dots,K-1\}$, read as the path from the root, with $|p|=m$. The edge enumeration $E_K(d)$ is the list given by $E_K(0)=()$ and
--   $$E_K(d+1)=\bigl((0),\ 0\cdot E_K(d),\ (1),\ 1\cdot E_K(d),\ \dots,\ (K-1),\ (K-1)\cdot E_K(d)\bigr),$$
--   where $i\cdot L$ denotes the list $L$ with the label $i$ prepended to every word; it lists every nonempty word of length at most $d$ (every edge of the depth-$d$ tree, identified with the path to its lower endpoint) exactly once, in depth-first preorder. Its length is the edge count $N_K(d)$, where $N_K(0)=0$ and $N_K(d+1)=K\,(1+N_K(d))$. The tree size is $S_K(0)=1$, $S_K(d+1)=1+K\,S_K(d)$; the preorder rank is $\operatorname{rank}_0(p)=0$, $\operatorname{rank}_{d+1}(\varnothing)=0$, $\operatorname{rank}_{d+1}((i,p_2,\dots,p_m))=1+i\,S_K(d)+\operatorname{rank}_d((p_2,\dots,p_m))$, and the edge rank is $\operatorname{erank}_d(p)=\operatorname{rank}_d(p)-1$ (truncated at $0$).
--
--   1. **Injective maps preserve positions.** If $f:\alpha\to\beta$ is injective, then for every $a\in\alpha$ and every list $L$ over $\alpha$, with $f(L)$ the elementwise image,
--   $$\operatorname{idx}_{f(L)}\bigl(f(a)\bigr)=\operatorname{idx}_L(a).$$
--
--   2. **Positions in a concatenation of blocks of equal length.** Let $L=(a_1,\dots,a_n)$ be a list over $\alpha$ and let $f$ assign to each element of $\alpha$ a list over $\beta$ of the same length $R$. If $a$ occurs in $L$, $b$ occurs in $f(a)$, and $b$ occurs in no $f(c)$ with $c\ne a$, then
--   $$\operatorname{idx}_{f(a_1)f(a_2)\cdots f(a_n)}(b)=\operatorname{idx}_L(a)\cdot R+\operatorname{idx}_{f(a)}(b).$$
--
--   3. **Size versus edge count.** $S_K(d)=1+N_K(d)$ for every $d$.
--
--   4. **Rank equals position.** For every word $p$ occurring in $E_K(d)$, that is, every nonempty word of length at most $d$,
--   $$\operatorname{rank}_d(p)=\operatorname{idx}_{E_K(d)}(p)+1,\qquad\operatorname{erank}_d(p)=\operatorname{idx}_{E_K(d)}(p).$$
--
--   The closed-form rank is convenient for inequalities (subtrees are intervals of ranks, siblings are ordered), whereas the listed enumeration is convenient for building lists of numerical data by recursion over the tree. These identities let results be transferred between the two descriptions.
--
--   **Formalization Note** Positions are `List.idxOf` (stated for types with lawful Boolean equality), and the concatenation of blocks is `List.flatMap`. The enumeration and count are `TreePreorder.edgePaths` and `TreePreorder.edgeCount`; size and ranks are `TreePreorderRank.size`, `rank` and `edgeRank`. All five members are theorems: `idxOf_map_injective`, `idxOf_flatMap_uniform`, `size_eq_one_add_edgeCount`, `rank_eq_idxOf_add_one` and `edgeRank_eq_idxOf`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/PreorderIndex.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/PreorderIndex.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DyadicAvoidance mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowData
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_StableRoutingBridge
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowExceptionalTransfer
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteWindowAtom
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicEnvelope
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GlobalFromPeriodic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridGeometry
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridMeasure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridStability
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowPlacement
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowRecursion
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PackedWindowSpan
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TreePreorder
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TreePreorderRank

namespace OAI

universe u_α u_β

namespace Problem310.PreorderIndex

 theorem idxOf_map_injective {α : Type u_α} {β : Type u_β} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hf : Function.Injective f) (a : α) (l : List α) :
    (l.map f).idxOf (f a) = l.idxOf a := by
  classical
  induction l with
  | nil => rfl
  | cons b l ih =>
    by_cases h : b = a
    · subst b
      simp
    · have hfba : f b ≠ f a := fun he => h (hf he)
      simp only [List.map_cons, List.idxOf_cons_ne _ hfba, List.idxOf_cons_ne _ h, ih]

 theorem idxOf_flatMap_uniform {α : Type u_α} {β : Type u_β} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (l : List α) (f : α → List β) (R : ℕ) (hlen : ∀ a, (f a).length = R)
    (a : α) (b : β) (ha : a ∈ l) (hb : b ∈ f a)
    (hdisjoint : ∀ c, c ≠ a → b ∉ f c) :
    (l.flatMap f).idxOf b = l.idxOf a * R + (f a).idxOf b := by
  classical
  induction l with
  | nil => simp at ha
  | cons c l ih =>
    by_cases hca : c = a
    · subst c
      rw [List.flatMap_cons, List.idxOf_append_of_mem hb]
      simp
    · have ha' : a ∈ l := by simpa [Ne.symm hca] using ha
      rw [List.flatMap_cons, List.idxOf_append_of_notMem (hdisjoint c hca),
        hlen c, ih ha', List.idxOf_cons_ne _ hca]
      simp only [Nat.succ_eq_add_one]
      ring

theorem size_eq_one_add_edgeCount (K d : ℕ) :
    TreePreorderRank.size K d = 1 + TreePreorder.edgeCount K d := by
  induction d with
  | zero => rfl
  | succ d ih => simp [TreePreorderRank.size, TreePreorder.edgeCount, ih]

/-- The arithmetic preorder rank agrees with the actual list enumeration.
The root is omitted from `edgePaths`, hence the offset by one. -/
theorem rank_eq_idxOf_add_one {K d : ℕ} {p : List (Fin K)}
    (hp : p ∈ TreePreorder.edgePaths K d) :
    TreePreorderRank.rank d p = (TreePreorder.edgePaths K d).idxOf p + 1 := by
  induction d generalizing p with
  | zero => simp at hp
  | succ d ih =>
    cases p with
    | nil => simp [TreePreorder.mem_edgePaths_iff] at hp
    | cons i p =>
      have hplen : p.length ≤ d := by
        have h := (TreePreorder.mem_edgePaths_iff K (d + 1) (i :: p)).mp hp
        simpa using h.2
      let block : Fin K → List (List (Fin K)) := fun j =>
        [j] :: (TreePreorder.edgePaths K d).map (List.cons j)
      have hlen (j : Fin K) : (block j).length = 1 + TreePreorder.edgeCount K d := by
        simp [block, Nat.add_comm]
      have hmem : i :: p ∈ block i := by
        by_cases hp0 : p = []
        · subst p
          simp [block]
        · apply List.mem_cons.mpr
          right
          apply List.mem_map.mpr
          exact ⟨p, (TreePreorder.mem_edgePaths_iff K d p).mpr ⟨hp0, hplen⟩, rfl⟩
      have hdisjoint (j : Fin K) (hji : j ≠ i) : i :: p ∉ block j := by
        intro hm
        obtain ⟨s, he⟩ := TreePreorder.mem_childBlock_prefix K d j (i :: p) hm
        exact hji (List.cons.inj he).1.symm
      have hindex := idxOf_flatMap_uniform (List.finRange K) block
        (1 + TreePreorder.edgeCount K d) hlen i (i :: p)
        (List.mem_finRange i) hmem hdisjoint
      simp only [List.idxOf_finRange] at hindex
      change (TreePreorder.edgePaths K (d + 1)).idxOf (i :: p) =
        i.val * (1 + TreePreorder.edgeCount K d) + (block i).idxOf (i :: p) at hindex
      rw [TreePreorderRank.rank_cons, hindex, size_eq_one_add_edgeCount]
      by_cases hp0 : p = []
      · subst p
        simp [block]
        omega
      · have hpedge := (TreePreorder.mem_edgePaths_iff K d p).mpr ⟨hp0, hplen⟩
        have hneq : [i] ≠ i :: p := by
          intro h
          exact hp0 (List.cons.inj h).2.symm
        have hbi : (block i).idxOf (i :: p) =
            (TreePreorder.edgePaths K d).idxOf p + 1 := by
          dsimp only [block]
          rw [List.idxOf_cons_ne _ hneq, idxOf_map_injective (List.cons i)
            (by intro a b h; exact (List.cons.inj h).2)]
        rw [hbi, ih hpedge]
        omega

theorem edgeRank_eq_idxOf {K d : ℕ} {p : List (Fin K)}
    (hp : p ∈ TreePreorder.edgePaths K d) :
    TreePreorderRank.edgeRank d p = (TreePreorder.edgePaths K d).idxOf p := by
  rw [TreePreorderRank.edgeRank, rank_eq_idxOf_add_one hp]
  omega

end Problem310.PreorderIndex

end OAI


