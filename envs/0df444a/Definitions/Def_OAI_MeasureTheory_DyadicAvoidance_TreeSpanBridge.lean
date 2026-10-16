-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TreeSpanBridge
-- name    : OAI_MeasureTheory_DyadicAvoidance_TreeSpanBridge
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T04:01:44.273708+00:00
-- url     : https://prove2.me/theorems/1e4a686c-35b9-473b-a706-9d2ce08bf4e7
-- title:
--   Edge weights in tree preorder and contiguity of descendant blocks
-- statement:
--   This file attaches a numerical weight to every edge of a complete ordered tree, lists the weights in depth-first preorder, and shows that the edges below any given edge form one contiguous block of that list. Fix $q\in\mathbb{N}$. Edges of the complete $q$-ary tree of depth $d$ are identified with the nonempty words $p=(p_1,\dots,p_m)$ over the labels $\{0,\dots,q-1\}$ with $|p|=m\le d$ (the path from the root to the lower endpoint). Let $E_q(d)$ be the list of these words in preorder: $E_q(0)=()$, and $E_q(d+1)$ is the concatenation over $i=0,\dots,q-1$ of the one-letter word $(i)$ followed by the list $E_q(d)$ with $i$ prepended to every word. For a list $L$ and an element $x$, $\operatorname{idx}_L(x)$ denotes the zero-based position of the first occurrence of $x$ in $L$. A list $X$ is an infix of a list $Y$ if $Y=UXV$ for some lists $U,V$.
--
--   1. **Weights.** For a function $r:\mathbb{N}\to\mathbb{N}$,
--   $$W_q(d,r)=\bigl(r(d+1-|p|)\bigr)_{p\in E_q(d)},$$
--   listed in the order of $E_q(d)$. The number $d+1-|p|$ is the height of the upper endpoint of the edge $p$, so each edge carries the value of $r$ at the height of the node it leaves.
--
--   2. **Subtree block.** For a word $p$, $B_d(p)$ is the list consisting of $p$ followed by the words $pv$ for $v$ running through $E_q(d-|p|)$: the edge $p$ and all edges below it, in preorder.
--
--   The file proves the following.
--
--   - $W_q(0,r)$ is empty, and $W_q(d+1,r)$ is the concatenation of $q$ copies of $\bigl(r(d+1),W_q(d,r)\bigr)$; in particular the weights of a child block do not depend on the child's label.
--   - For every label $i$, the list consisting of $(i)$ followed by $E_q(d)$ with $i$ prepended is an infix of $E_q(d+1)$. More generally, for every nonempty word $p$ with $|p|\le d$, the block $B_d(p)$ is an infix of $E_q(d)$.
--   - If $|p|\le d$, then the weights $r(d+1-|v|)$ of the words $v$ of $B_d(p)$, in order, form the list $\bigl(r(d+1-|p|),W_q(d-|p|,r)\bigr)$.
--   - Let $g,r_0\in\mathbb{N}$ and let $\ell$ be the window length of the window recursion with branching $q$: $\sigma(0)=0$, $\ell(0)=r_0$, $\ell(h+1)=\max(r_0,g+\sigma(h))$ and $\sigma(h+1)=q\,c(h)+(q-1)g$ (with $q-1$ truncated at $0$), where $c(0)=\ell(1)$ and $c(h)=\ell(h+1)+g+\sigma(h)$ for $h\ge1$. Let $\Lambda(0)=()$ and let $\Lambda(h+1)$ be the concatenation of $q$ copies of $\bigl(\ell(h+1),\Lambda(h)\bigr)$. Then $W_q(d,\ell)=\Lambda(d)$ for every $d$.
--   - Decomposition at an edge: for every nonempty word $p$ with $|p|\le d$ there are lists $U,V$ of natural numbers such that
--   $$W_q(d,\ell)=U\,\bigl(\ell(d+1-|p|),\ \Lambda(d-|p|)\bigr)\,V\qquad\text{and}\qquad|U|=\operatorname{idx}_{E_q(d)}(p).$$
--
--   The decomposition locates the window lengths of an edge and of all edges below it as one consecutive segment of the global preorder list, starting exactly at the position of the edge. Combined with the padded-sum bound for such a segment, it controls where the windows below an edge can end.
--
--   **Formalization Note** The definitions are `weights q d r` (built from `TreePreorder.edgePaths`) and `subtreeBlock q d p`; infixes are `List.IsInfix`, positions are `List.idxOf`. $\ell$ and $\Lambda$ are `WindowRecursion.length q g r₀` and `WindowSpanSum.preorderLengths q g r₀`. The subtractions $d+1-|p|$ and $d-|p|$ are truncated natural-number subtractions, which agree with the usual ones under the stated length bounds.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/TreeSpanBridge.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/TreeSpanBridge.lean by skeleton subtraction
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

namespace OAI

universe u_α

namespace Problem310.TreeSpanBridge

open TreePreorder

/-- Incoming-window lengths listed in the tree's edge preorder. -/
def weights (q d : ℕ) (r : ℕ → ℕ) : List ℕ :=
  (edgePaths q d).map fun p => r (d + 1 - p.length)

@[simp] theorem weights_zero (q : ℕ) (r : ℕ → ℕ) : weights q 0 r = [] := rfl

/-- Each child contributes its incoming length followed by the weights of a
complete subtree of one smaller height. This is independent of the child label. -/
theorem weights_succ (q d : ℕ) (r : ℕ → ℕ) :
    weights q (d + 1) r =
      (List.finRange q).flatMap (fun _ => r (d + 1) :: weights q d r) := by
  simp only [weights, edgePaths, List.map_flatMap, List.map_cons,
    List.length_cons, List.map_map, Function.comp_def]
  congr 2
  funext i
  congr 1
  apply List.map_congr_left
  intro p hp
  congr 1
  omega

/-- An edge and all descendants under it, in their contiguous preorder block. -/
def subtreeBlock (q d : ℕ) (p : List (Fin q)) : List (List (Fin q)) :=
  p :: (edgePaths q (d - p.length)).map (fun v => p ++ v)

theorem childBlock_infix (q d : ℕ) (i : Fin q) :
    ([i] :: (edgePaths q d).map (List.cons i)) <:+: edgePaths q (d + 1) := by
  have hi : [i] <:+: List.finRange q := (List.singleton_infix_iff i (List.finRange q)).mpr (by simp)
  simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, edgePaths] using
    hi.flatMap (fun j => [j] :: (edgePaths q d).map (List.cons j))

/-- Every rooted descendant block is contiguous in the global edge preorder. -/
theorem subtreeBlock_infix (q d : ℕ) (p : List (Fin q))
    (hp : p ≠ []) (hlen : p.length ≤ d) :
    subtreeBlock q d p <:+: edgePaths q d := by
  induction p generalizing d with
  | nil => exact (hp rfl).elim
  | cons i p ih =>
    cases d with
    | zero => simp at hlen
    | succ d =>
      cases p with
      | nil =>
        simpa [subtreeBlock] using childBlock_infix q d i
      | cons j p =>
        have hlen' : (j :: p).length ≤ d := by simpa using hlen
        have hsub := (ih d (by simp) hlen').map (List.cons i)
        have htail : (edgePaths q d).map (List.cons i) <:+:
            [i] :: (edgePaths q d).map (List.cons i) :=
          ⟨[[i]], [], by simp⟩
        have hfull := hsub.trans (htail.trans (childBlock_infix q d i))
        simpa [subtreeBlock, List.map_map, Function.comp_def] using hfull

/-- Global-depth weights on one descendant block are exactly the incoming
length followed by the weights of the complete residual-height subtree. -/
theorem map_weights_subtreeBlock (q d : ℕ) (r : ℕ → ℕ) (p : List (Fin q))
    (hlen : p.length ≤ d) :
    (subtreeBlock q d p).map (fun v => r (d + 1 - v.length)) =
      r (d + 1 - p.length) :: weights q (d - p.length) r := by
  simp only [subtreeBlock, List.map_cons, List.map_map, Function.comp_def,
    List.length_append, weights]
  congr 1
  apply List.map_congr_left
  intro v hv
  congr 1
  omega

/-- The path-dependent weight list is exactly the numerical preorder list. -/
theorem weights_eq_preorderLengths (q g r₀ d : ℕ) :
    weights q d (WindowRecursion.length q g r₀) =
      WindowSpanSum.preorderLengths q g r₀ d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [weights_succ, WindowSpanSum.preorderLengths, ih]
    simp [List.flatMap]

/-- Full-list decomposition at the genuine edge index. This is the direct
interface for constructing separated windows from the weighted preorder. -/
theorem weighted_child_decomposition (q g r₀ d : ℕ) (p : List (Fin q))
    (hp : p ≠ []) (hlen : p.length ≤ d) :
    ∃ pre post : List ℕ,
      weights q d (WindowRecursion.length q g r₀) =
        pre ++ (WindowRecursion.length q g r₀ (d + 1 - p.length) ::
          WindowSpanSum.preorderLengths q g r₀ (d - p.length)) ++ post ∧
      pre.length = (edgePaths q d).idxOf p := by
  obtain ⟨s, t, hst⟩ := subtreeBlock_infix q d p hp hlen
  let f : List (Fin q) → ℕ := fun v => WindowRecursion.length q g r₀ (d + 1 - v.length)
  refine ⟨s.map f, t.map f, ?_, ?_⟩
  · change (edgePaths q d).map f = _
    rw [← hst, List.map_append, List.map_append]
    change s.map f ++ (subtreeBlock q d p).map
      (fun v => WindowRecursion.length q g r₀ (d + 1 - v.length)) ++ t.map f = _
    rw [map_weights_subtreeBlock q d _ p hlen, weights_eq_preorderLengths]
  · rw [List.length_map]
    have hnodup : (s ++ (subtreeBlock q d p ++ t)).Nodup := by
      rw [← List.append_assoc, hst]
      exact nodup_edgePaths q d
    have hnot : p ∉ s := by
      intro hps
      exact (List.nodup_append.mp hnodup).2.2 p hps p (by simp [subtreeBlock]) rfl
    rw [← hst, List.append_assoc, List.idxOf_append_of_notMem hnot]
    simp [subtreeBlock]

end Problem310.TreeSpanBridge

end OAI


