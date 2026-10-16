-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowMetadata
-- name    : OAI_MeasureTheory_DyadicAvoidance_WindowMetadata
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T04:07:51.972589+00:00
-- url     : https://prove2.me/theorems/fd477bbd-fd3d-4a99-b7f3-08d9a5e51dcd
-- title:
--   Canonical windows of consecutive indices attached to the edges of a complete tree
-- statement:
--   This file attaches to every edge of a complete ordered tree a window of consecutive natural numbers, by laying the windows out in the canonical depth-first order of the edges, and records their sizes and membership. Fix natural numbers $q$ (the number of children of each node), $d$ (the depth), $g$ (the gap) and $r_0$ (the minimum window length). An edge of the complete $q$-ary tree of depth $d$ is a nonempty word $e=(e_1,\dots,e_m)$ over $\{0,\dots,q-1\}$ with $|e|=m\le d$, the path from the root to its lower endpoint; let $\mathcal{E}_q(d)$ be the finite set of edges and $E_q(d)$ the list of edges in depth-first preorder ($E_q(0)=()$, and $E_q(d+1)$ concatenates, for $i=0,\dots,q-1$, the word $(i)$ and the list $E_q(d)$ with $i$ prepended to every word).
--
--   Window lengths are given by the window recursion: $\sigma(0)=0$, $\ell(0)=r_0$, and for $h\ge0$
--   $$\ell(h+1)=\max\bigl(r_0,\ g+\sigma(h)\bigr),\qquad\sigma(h+1)=q\,c(h)+(q-1)\,g,$$
--   where $c(0)=\ell(1)$, $c(h)=\ell(h+1)+g+\sigma(h)$ for $h\ge1$, and $q-1$ is truncated at $0$. For a length sequence $\lambda:\mathbb{N}\to\mathbb{N}$ the placement is $s_\lambda(0)=3$, $s_\lambda(n+1)=s_\lambda(n)+\lambda(n)+g$ and $f_\lambda(n)=s_\lambda(n)+\lambda(n)-1$.
--
--   1. **Edge index.** $\iota(e)$ is the zero-based position of the edge $e$ in $E_q(d)$.
--
--   2. **Edge height.** $\eta(e)=d+1-|e|$, the height of the upper endpoint of $e$.
--
--   3. **Lengths.** $L=\bigl(\ell(d+1-|P|)\bigr)_{P\in E_q(d)}$ in preorder, and $\lambda(n)$ is the $n$-th entry of $L$ (counting from $0$), or $0$ if $n\ge|L|$.
--
--   4. **Start, finish and window.** For $e\in\mathcal{E}_q(d)$: $s(e)=s_\lambda(\iota(e))$, $f(e)=f_\lambda(\iota(e))$ and $\mathrm{win}(e)=\{n\in\mathbb{N}:\ s(e)\le n\le f(e)\}$.
--
--   For every edge $e$ the file proves
--   $$\lambda(\iota(e))=\ell(\eta(e)),\qquad\#\,\mathrm{win}(e)=\ell(\eta(e)),\qquad n\in\mathrm{win}(e)\iff s(e)\le n\le f(e),$$
--   and, for every word $P$ with $|P|<d$ and every label $i$, the child edge $Pi$ (the word $P$ followed by $i$) has height $d-|P|$ and a window with $\ell(d-|P|)$ elements.
--
--   Consecutive windows in preorder are separated by exactly $g$ unused indices, and the size of each window depends only on the height of its edge. This packages the preorder window placement as data indexed directly by the finite set of edges, so that start, finish, size and membership of the window of an edge, in particular of a child edge, can be read off without passing through list positions.
--
--   **Formalization Note** `Edge q d` is the subtype of words `List (Fin q)` belonging to `TreePreorder.edgePaths q d`; `childEdge P hP i` is the edge `P ++ [i]`. The definitions are `edgeIndex` (via `List.idxOf`), `edgeHeight`, `lengths`, `lengthAt`, `start`, `finish` and `window` (a `Finset.Icc`), built on `WindowPlacement` and `WindowRecursion.length`; the lemmas are `lengthAt_edgeIndex`, `card_window`, `mem_window`, `child_height` and `child_window_card`. No assumptions on $q$, $g$ or $r_0$ are needed; $f_\lambda$ uses truncated subtraction, which is exact because $s_\lambda\ge3$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/WindowMetadata.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/WindowMetadata.lean by skeleton subtraction
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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowDataExistence

namespace OAI

noncomputable section

namespace Problem310.WindowMetadata

open TreePreorder

/-- The canonical preorder index of an edge. -/
def edgeIndex {q d : ℕ} (e : Edge q d) : ℕ := (edgePaths q d).idxOf e.val

/-- Numeric incoming-window height for an edge path. -/
def edgeHeight {q d : ℕ} (e : Edge q d) : ℕ := d + 1 - e.val.length

/-- Window lengths in precisely the canonical tree-edge preorder. -/
def lengths (q d g r₀ : ℕ) : List ℕ :=
  (edgePaths q d).map (fun P => WindowRecursion.length q g r₀ (d + 1 - P.length))

/-- The length function consumed by the canonical numeric placement API. -/
def lengthAt (q d g r₀ : ℕ) : ℕ → ℕ :=
  WindowPlacement.lengthAt (lengths q d g r₀)

def start {q d : ℕ} (g r₀ : ℕ) (e : Edge q d) : ℕ :=
  WindowPlacement.start (lengthAt q d g r₀) g (edgeIndex e)

def finish {q d : ℕ} (g r₀ : ℕ) (e : Edge q d) : ℕ :=
  WindowPlacement.finish (lengthAt q d g r₀) g (edgeIndex e)

def window {q d : ℕ} (g r₀ : ℕ) (e : Edge q d) : Finset ℕ :=
  WindowPlacement.window (lengthAt q d g r₀) g (edgeIndex e)

@[simp] theorem lengthAt_edgeIndex {q d : ℕ} (g r₀ : ℕ) (e : Edge q d) :
    lengthAt q d g r₀ (edgeIndex e) = WindowRecursion.length q g r₀ (edgeHeight e) := by
  simp only [lengthAt, lengths, WindowPlacement.lengthAt, edgeIndex,
    List.getElem?_map, List.getElem?_idxOf e.property, Option.map_some, Option.getD_some,
    edgeHeight]

@[simp] theorem card_window {q d : ℕ} (g r₀ : ℕ) (e : Edge q d) :
    (window g r₀ e).card = WindowRecursion.length q g r₀ (edgeHeight e) := by
  simp only [window, WindowPlacement.card_window, lengthAt_edgeIndex]

@[simp] theorem mem_window {q d : ℕ} {g r₀ n : ℕ} {e : Edge q d} :
    n ∈ window g r₀ e ↔ start g r₀ e ≤ n ∧ n ≤ finish g r₀ e :=
  WindowPlacement.mem_window

@[simp] theorem child_height {q d : ℕ} (P : List (Fin q)) (hP : P.length < d)
    (i : Fin q) : edgeHeight (childEdge P hP i) = d - P.length := by
  simp [edgeHeight, childEdge, mkEdge]

@[simp] theorem child_window_card {q d : ℕ} (g r₀ : ℕ)
    (P : List (Fin q)) (hP : P.length < d) (i : Fin q) :
    (window g r₀ (childEdge P hP i)).card =
      WindowRecursion.length q g r₀ (d - P.length) := by
  rw [card_window, child_height]

end Problem310.WindowMetadata

end

end OAI


