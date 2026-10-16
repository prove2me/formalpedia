-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PackedWindowSpan
-- name    : OAI_MeasureTheory_DyadicAvoidance_PackedWindowSpan
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:50:47.380824+00:00
-- url     : https://prove2.me/theorems/3781e47f-0982-4aa5-be5d-96fe53b6c535
-- title:
--   Packed span of a list of windows and the preorder list of window lengths
-- statement:
--   Fix natural numbers $M$, $g$ and $r_0$, and recall the window-length recursion for the complete ordered tree in which every internal vertex has $M$ children: $\sigma_0=0$, $\ell_0=r_0$, $\ell_{h+1}=\max(r_0,\,g+\sigma_h)$ and $\sigma_{h+1}=M\big(\ell_{h+1}+[h\ge1]\,(g+\sigma_h)\big)+\max(M-1,0)\,g$, where $[h\ge1]$ is $1$ for $h\ge1$ and $0$ for $h=0$. Here $\ell_h$ is the window length of an edge whose parent vertex has height $h$, and $\sigma_h$ is the span of a complete subtree of height $h$.
--
--   1. **Packed span.** For a finite list $L=(L_1,\dots,L_m)$ of natural numbers and a gap $g$,
--   $$\mathrm{span}_g(L)=\sum_{j=1}^{m}L_j+\max(m-1,0)\,g,$$
--   the number of indices occupied by windows of lengths $L_1,\dots,L_m$ placed consecutively with $g$ unused indices between neighbours and no leading or trailing gap. In particular the empty list has packed span $0$ and a one-element list $(r)$ has packed span $r$.
--   2. **Preorder length list.** $\Lambda_0$ is the empty list and
--   $$\Lambda_{h+1}=\underbrace{(\ell_{h+1})\,\Vert\,\Lambda_h\,\Vert\,(\ell_{h+1})\,\Vert\,\Lambda_h\,\Vert\cdots\Vert\,(\ell_{h+1})\,\Vert\,\Lambda_h}_{M\ \text{blocks}},$$
--   where $\Vert$ denotes concatenation of lists. Thus $\Lambda_h$ lists the window lengths of all edges of the complete ordered tree of height $h$ in depth-first preorder: in $\Lambda_{h+1}$, each of the $M$ children of the root contributes the length $\ell_{h+1}$ of its incoming edge, followed by the list $\Lambda_h$ of its own subtree of height $h$.
--
--   These objects identify the recursively defined span with the actual layout of the windows: for $M\ge1$ one has $\mathrm{span}_g(\Lambda_h)=\sigma_h$, so the numerical recursion measures exactly the block of indices occupied by a complete subtree when windows are placed in preorder with gaps of size $g$. This is an ingredient in building the deterministic index windows for the construction of a compact set avoiding the affine copies $\{x+s\,2^{-n}:n\ge1\}$, $s\neq0$, of the dyadic sequence.
--
--   **Formalization Note** `packedSpan g L` is `L.sum + (L.length - 1) * g` with natural-number subtraction, which gives $0$ for the empty list; `preorderLengths M g r₀` is built with `List.replicate` and `List.flatten` from the lengths `WindowRecursion.length M g r₀`. The simp lemmas `packedSpan_nil`, `packedSpan_singleton` and `preorderLengths_zero` record the base cases.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/PackedWindowSpan.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/PackedWindowSpan.lean by skeleton subtraction
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

namespace OAI

namespace Problem310.WindowRecursion

/-- Length of a list of windows packed with a fixed gap between consecutive
windows, with no leading or trailing gap. -/
def packedSpan (g : ℕ) (L : List ℕ) : ℕ := L.sum + (L.length - 1) * g

@[simp] theorem packedSpan_nil (g : ℕ) : packedSpan g [] = 0 := by
  simp [packedSpan]

@[simp] theorem packedSpan_singleton (g r : ℕ) : packedSpan g [r] = r := by
  simp [packedSpan]

/-- The deterministic list of incoming-window lengths in full preorder. -/
def preorderLengths (M g r₀ : ℕ) : ℕ → List ℕ
  | 0 => []
  | h + 1 => (List.replicate M (length M g r₀ (h + 1) :: preorderLengths M g r₀ h)).flatten

@[simp] theorem preorderLengths_zero (M g r₀ : ℕ) : preorderLengths M g r₀ 0 = [] := rfl

end Problem310.WindowRecursion

end OAI


