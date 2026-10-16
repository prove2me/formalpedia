-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowDataExistence
-- name    : OAI_MeasureTheory_DyadicAvoidance_WindowDataExistence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T04:03:05.618909+00:00
-- url     : https://prove2.me/theorems/f6f94162-a759-477e-9c62-e10e7767b90d
-- title:
--   Explicit nested, gapped and padded index windows on the edges of a complete tree
-- statement:
--   This file constructs, for a complete ordered tree, an explicit system of windows of consecutive natural numbers, one window per edge, and proves that it satisfies the axioms of window data used by the routing construction. Fix natural numbers $q$ (the number of children of each node), $d$ (the depth), $g$ (the gap) and $r_0$ (the minimum window length). Edges of the complete $q$-ary tree of depth $d$ are identified with nonempty words $P=(P_1,\dots,P_m)$ over $\{0,\dots,q-1\}$ of length $|P|=m\le d$ (the path from the root to the lower endpoint); such a $P$ is called a valid edge. Let $E_q(d)$ be the list of valid edges in depth-first preorder, let $\operatorname{erank}_d(P)$ be the zero-based position of $P$ in it, and let $N_q(h)$ be the number of edges of the complete tree of height $h$, i.e. $N_q(0)=0$ and $N_q(h+1)=q\,(1+N_q(h))$.
--
--   Window lengths come from the window recursion: $\sigma(0)=0$, $\ell(0)=r_0$ and, for $h\ge0$,
--   $$\ell(h+1)=\max\bigl(r_0,\ g+\sigma(h)\bigr),\qquad\sigma(h+1)=q\,c(h)+(q-1)\,g,$$
--   where $c(0)=\ell(1)$, $c(h)=\ell(h+1)+g+\sigma(h)$ for $h\ge1$, and $q-1$ is truncated at $0$. Let $\Lambda(0)=()$ and let $\Lambda(h+1)$ be the concatenation of $q$ copies of $\bigl(\ell(h+1),\Lambda(h)\bigr)$. Windows are placed along a length sequence $\lambda:\mathbb{N}\to\mathbb{N}$ by
--   $$s_\lambda(0)=3,\qquad s_\lambda(n+1)=s_\lambda(n)+\lambda(n)+g,\qquad f_\lambda(n)=s_\lambda(n)+\lambda(n)-1,$$
--   so that the $n$-th window $\{s_\lambda(n),\dots,f_\lambda(n)\}$ has $\lambda(n)$ elements and is followed by $g$ unused indices.
--
--   **Window data.** A window datum with parameters $(q,d,g,r_0)$ consists of a length function $r:\mathbb{N}\to\mathbb{N}$ and maps $a,b,b^{*}$ from words to $\mathbb{N}$ such that, writing $r_P=r(d+1-|P|)$, the following hold for all valid edges $P,Q$:
--
--   - (i) $1\le r_P$ and $r_0\le r_P$;
--   - (ii) $3\le a(P)$ and $b(P)+1=a(P)+r_P$;
--   - (iii) if $P$ is a proper prefix of $Q$, then $b(P)+g<a(Q)$;
--   - (iv) if $i<j$ are labels, $t$ is a word, and $Pi$ and $Pjt$ are valid edges, then $b(Pi)+g<a(Pjt)$;
--   - (v) if $P$ is a prefix of $Q$, then $b(P)\le b(Q)\le b^{*}(P)$;
--   - (vi) $b^{*}(P)+1\le a(P)+2\,r_P$.
--
--   The file defines:
--
--   1. **Length list.** $L=\bigl(\ell(d+1-|P|)\bigr)_{P\in E_q(d)}$, the window lengths in preorder, each edge receiving $\ell$ at the height $d+1-|P|$ of its upper endpoint.
--
--   2. **Length sequence.** $\lambda(n)$ is the $n$-th entry of $L$ (counting from $0$), and $\lambda(n)=0$ when $n\ge|L|$.
--
--   3. **The window datum.** For $q\ge1$ and $r_0\ge1$, the window datum with $r=\ell$ and
--   $$a(P)=s_\lambda\bigl(\operatorname{erank}_d(P)\bigr),\qquad b(P)=f_\lambda\bigl(\operatorname{erank}_d(P)\bigr),\qquad b^{*}(P)=a(P)+2\,\ell(d+1-|P|)-1 .$$
--
--   Along the way it proves that $\lambda(\operatorname{erank}_d(P))=\ell(d+1-|P|)$ for every valid edge $P$, that $\Lambda(h)$ has exactly $N_q(h)$ entries, and the descendant endpoint bound: if $q\ge1$, $P$ and $Q$ are valid edges and $P$ is a prefix of $Q$, then
--   $$f_\lambda\bigl(\operatorname{erank}_d(Q)\bigr)+1\le s_\lambda\bigl(\operatorname{erank}_d(P)\bigr)+2\,\ell(d+1-|P|).$$
--
--   So window data exist for every branching number $q\ge1$, every depth $d$, every gap $g$ and every threshold $r_0\ge1$. In the constructed system the window of an edge has length at least $r_0$ depending only on the edge's height, it precedes the windows of all edges below it and of all later siblings' subtrees with at least $g$ unused indices in between, and all windows below an edge end within twice that edge's window length from its start. These are the deterministic properties of the windows on which the routing argument and its probabilistic estimates rely.
--
--   **Formalization Note** The structure is `WindowData q d g r₀` with fields `r`, `a`, `b`, `bstar` and the axioms `length_pos`, `length_threshold`, `start_three`, `endpoint`, `gap_prefix`, `gap_sibling`, `descendant_bounds`, `padding`; valid edges are `ValidWindowEdge d P`. The file defines `lengths`, `lengthAt` (via `WindowPlacement.lengthAt`, which returns $0$ outside the list) and `windowData q d g r₀ hq hr₀`, and proves `lengthAt_edgeRank`, `length_preorderLengths` and `descendant_endpoint_bound`. The placement is `WindowPlacement.start` and `WindowPlacement.finish`; the truncated subtraction in $b^{*}$ is harmless because $a(P)\ge3$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/WindowDataExistence.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/WindowDataExistence.lean by skeleton subtraction
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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PreorderIndex
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowSpanSum
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TreeSpanBridge

namespace OAI

noncomputable section

namespace Problem310.WindowConstruction

open TreePreorder TreePreorderRank WindowPlacement
open scoped BigOperators

/-- Actual window lengths, in the finite tree preorder. -/
def lengths (q d g r₀ : ℕ) : List ℕ :=
  TreeSpanBridge.weights q d (WindowRecursion.length q g r₀)

def lengthAt (q d g r₀ : ℕ) : ℕ → ℕ := WindowPlacement.lengthAt (lengths q d g r₀)

lemma lengthAt_edgeRank {q d g r₀ : ℕ} {P : List (Fin q)}
    (hP : ValidWindowEdge d P) :
    lengthAt q d g r₀ (edgeRank d P) = WindowRecursion.length q g r₀ (d + 1 - P.length) := by
  have hm := (mem_edgePaths_iff q d P).mpr hP
  rw [PreorderIndex.edgeRank_eq_idxOf hm]
  exact WindowPlacement.lengthAt_map_idxOf _ hm

lemma length_preorderLengths (q g r₀ h : ℕ) :
    (WindowSpanSum.preorderLengths q g r₀ h).length = edgeCount q h := by
  rw [← TreeSpanBridge.weights_eq_preorderLengths q g r₀ h]
  simp [TreeSpanBridge.weights]

/-- Every descendant endpoint lies within twice the incoming window length. -/
theorem descendant_endpoint_bound {q d g r₀ : ℕ} (hq : 1 ≤ q)
    {P Q : List (Fin q)} (hP : ValidWindowEdge d P) (hQ : ValidWindowEdge d Q)
    (hpref : P.IsPrefix Q) :
    finish (lengthAt q d g r₀) g (edgeRank d Q) + 1 ≤
      start (lengthAt q d g r₀) g (edgeRank d P) +
        2 * WindowRecursion.length q g r₀ (d + 1 - P.length) := by
  obtain ⟨pre, post, hL, hpre⟩ :=
    TreeSpanBridge.weighted_child_decomposition q g r₀ d P hP.1 hP.2
  have hmem := (mem_edgePaths_iff q d P).mpr hP
  have hpre' : pre.length = edgeRank d P := by
    rw [PreorderIndex.edgeRank_eq_idxOf hmem]
    exact hpre
  have hheight : d + 1 - P.length = (d - P.length) + 1 := by
    have hlen := hP.2
    omega
  let block := WindowRecursion.length q g r₀ (d + 1 - P.length) ::
    WindowSpanSum.preorderLengths q g r₀ (d - P.length)
  have hcard : block.length = edgeCount q (d - P.length) + 1 := by
    simp [block, length_preorderLengths]
  have hsum := WindowPlacement.sum_lengthAt_segment pre block post g
  have hL' : lengths q d g r₀ = pre ++ block ++ post := hL
  rw [← hL', hcard, hpre'] at hsum
  have hbudget :
      (∑ k ∈ Finset.range (edgeCount q (d - P.length) + 1),
        (lengthAt q d g r₀ (edgeRank d P + k) + g)) ≤
      2 * WindowRecursion.length q g r₀ (d + 1 - P.length) + g := by
    change (∑ k ∈ Finset.range (edgeCount q (d - P.length) + 1),
      (WindowPlacement.lengthAt (lengths q d g r₀) (edgeRank d P + k) + g)) ≤ _
    rw [hsum]
    change WindowSpanSum.paddedSum g block ≤ _
    dsimp [block]
    rw [hheight]
    exact WindowSpanSum.childBlock_budget q g r₀ (d - P.length) hq
  have hend := WindowPlacement.block_endpoint_le hbudget
  have hr := (isPrefix_iff_edgeRank_bounds hP.2 hQ.2 hP.1 hQ.1).mp hpref
  rw [PreorderIndex.size_eq_one_add_edgeCount] at hr
  have hle : edgeRank d Q ≤ edgeRank d P + edgeCount q (d - P.length) := by omega
  have hm := WindowPlacement.finish_mono (lengthAt q d g r₀) g hle
  omega

/-- The complete deterministic windows exist with any prescribed positive
uniform threshold and gap. -/
def windowData (q d g r₀ : ℕ) (hq : 1 ≤ q) (hr₀ : 1 ≤ r₀) :
    WindowData q d g r₀ where
  r := WindowRecursion.length q g r₀
  a P := start (lengthAt q d g r₀) g (edgeRank d P)
  b P := finish (lengthAt q d g r₀) g (edgeRank d P)
  bstar P := start (lengthAt q d g r₀) g (edgeRank d P) +
    2 * WindowRecursion.length q g r₀ (d + 1 - P.length) - 1
  length_pos P hP := hr₀.trans (WindowRecursion.threshold_le_length _ _ _ _)
  length_threshold P hP := WindowRecursion.threshold_le_length _ _ _ _
  start_three P hP := WindowPlacement.three_le_start _ _ _
  endpoint P hP := by
    rw [WindowPlacement.finish_add_one, lengthAt_edgeRank hP]
  gap_prefix P Q hP hQ hpref hne := by
    apply WindowPlacement.gap_of_lt
    have hr := (isPrefix_iff_edgeRank_bounds hP.2 hQ.2 hP.1 hQ.1).mp hpref
    apply lt_of_le_of_ne hr.1
    intro heq
    exact hne (edgeRank_injective_on hP.2 hQ.2 hP.1 hQ.1 heq)
  gap_sibling P i j tail hij hP hQ := by
    apply WindowPlacement.gap_of_lt
    exact edgeRank_sibling_descendants_lt (p := []) hij hP.2 hQ.2
  descendant_bounds P Q hP hQ hpref := by
    constructor
    · apply WindowPlacement.finish_mono
      exact ((isPrefix_iff_edgeRank_bounds hP.2 hQ.2 hP.1 hQ.1).mp hpref).1
    · have hb := descendant_endpoint_bound (g := g) (r₀ := r₀) hq hP hQ hpref
      omega
  padding P hP := by
    have hstart := WindowPlacement.three_le_start (lengthAt q d g r₀) g (edgeRank d P)
    omega

end Problem310.WindowConstruction

end

end OAI


