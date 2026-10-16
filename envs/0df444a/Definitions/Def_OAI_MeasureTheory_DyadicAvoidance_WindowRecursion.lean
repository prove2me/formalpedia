-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowRecursion
-- name    : OAI_MeasureTheory_DyadicAvoidance_WindowRecursion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:48:50.965403+00:00
-- url     : https://prove2.me/theorems/a5a5cf75-848d-4100-87c5-f3d53a51d142
-- title:
--   Window lengths and subtree spans for a complete tree, with the padding bound $c_h\le 2\ell_{h+1}$
-- statement:
--   Fix natural numbers $M$ (the number of children of each internal vertex), $g$ (the gap between consecutive windows) and $r_0$ (a lower threshold for window lengths). Write $[h\ge1]$ for $1$ if $h\ge1$ and $0$ if $h=0$, and $(M-1)_+=\max(M-1,0)$. The file defines three sequences indexed by the height $h\in\mathbb{N}$.
--
--   1. **Span.** $\sigma_0=0$ and
--   $$\sigma_{h+1}=M\Big(\max(r_0,\,g+\sigma_h)+[h\ge1]\,(g+\sigma_h)\Big)+(M-1)_+\,g.$$
--   2. **Window length.** $\ell_0=r_0$ and $\ell_{h+1}=\max(r_0,\,g+\sigma_h)$.
--   3. **Child span.** $c_h=\ell_{h+1}+[h\ge1]\,(g+\sigma_h)$.
--
--   In the complete ordered tree in which every internal vertex has $M$ children, $\ell_h$ is the length of the index window attached to an edge whose parent vertex has height $h\ge1$ (the value $\ell_0=r_0$ is a placeholder), $\sigma_h$ is the total span of the windows of a complete subtree of height $h$, including the gaps between consecutive windows but no leading or trailing gap, and $c_h$ is the span of one edge leaving a vertex of height $h+1$: its window followed, when the child is not a leaf, by one gap and the complete subtree of height $h$ below the child. The file proves $\sigma_{h+1}=Mc_h+(M-1)_+\,g$, $c_0=\ell_1$, $\sigma_1=M\ell_1+(M-1)_+\,g$, $c_{h+1}=\ell_{h+2}+g+\sigma_{h+1}$, $r_0\le\ell_h$, $g+\sigma_h\le\ell_{h+1}$, and the padding estimate
--   $$c_h\le2\,\ell_{h+1}\qquad\text{for all }h\in\mathbb{N}.$$
--
--   The recursion is bottom-up: every window is at least the threshold $r_0$ and at least one gap plus the whole span below it. Consequently an entire child block occupies at most twice the length of its incoming window, independently of the height of the tree. In the construction of a compact set avoiding the affine copies $\{x+s\,2^{-n}:n\ge1\}$, $s\neq0$, of the dyadic sequence, this bounds the range of dyadic indices used below an edge by twice that edge's own window length, while the threshold $r_0$ guarantees enough trials in every window.
--
--   **Formalization Note** The sequences are `span M g r₀`, `length M g r₀` and `childSpan M g r₀`, with $(M-1)_+$ written as the natural-number subtraction `M - 1`. The listed facts are `span_succ`, `childSpan_zero`, `span_one`, `childSpan_succ`, `threshold_le_length`, `gap_add_span_le_length` and `childSpan_le_twice_length`, together with the defining simp lemmas `span_zero`, `length_zero` and `length_succ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/WindowRecursion.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/WindowRecursion.lean by skeleton subtraction
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

namespace OAI

namespace Problem310.WindowRecursion

/-- Total span occupied by the windows in a complete tree of the given height.
At a bottom-level child there is no following subtree gap; at higher levels the
incoming window is followed by one gap and the complete child subtree. -/
def span (M g r₀ : ℕ) : ℕ → ℕ
  | 0 => 0
  | h + 1 =>
      M * (max r₀ (g + span M g r₀ h) +
        if h = 0 then 0 else g + span M g r₀ h) + (M - 1) * g

/-- Length of an incoming window whose parent has height `h + 1`.
The value at height zero is unused and is set equal to the threshold. -/
def length (M g r₀ : ℕ) : ℕ → ℕ
  | 0 => r₀
  | h + 1 => max r₀ (g + span M g r₀ h)

/-- Span of one incoming-edge window and the subtree beneath that edge. -/
def childSpan (M g r₀ h : ℕ) : ℕ :=
  length M g r₀ (h + 1) + if h = 0 then 0 else g + span M g r₀ h

@[simp] theorem span_zero (M g r₀ : ℕ) : span M g r₀ 0 = 0 := rfl

@[simp] theorem length_zero (M g r₀ : ℕ) : length M g r₀ 0 = r₀ := rfl

@[simp] theorem length_succ (M g r₀ h : ℕ) :
    length M g r₀ (h + 1) = max r₀ (g + span M g r₀ h) := rfl

theorem span_succ (M g r₀ h : ℕ) :
    span M g r₀ (h + 1) = M * childSpan M g r₀ h + (M - 1) * g := rfl

@[simp] theorem childSpan_zero (M g r₀ : ℕ) :
    childSpan M g r₀ 0 = length M g r₀ 1 := by
  simp [childSpan]

@[simp] theorem span_one (M g r₀ : ℕ) :
    span M g r₀ 1 = M * length M g r₀ 1 + (M - 1) * g := by
  rw [span_succ, childSpan_zero]

theorem childSpan_succ (M g r₀ h : ℕ) :
    childSpan M g r₀ (h + 1) =
      length M g r₀ (h + 2) + g + span M g r₀ (h + 1) := by
  simp [childSpan, Nat.add_assoc]

theorem threshold_le_length (M g r₀ h : ℕ) : r₀ ≤ length M g r₀ h := by
  cases h with
  | zero => exact le_rfl
  | succ h => exact le_max_left _ _

theorem gap_add_span_le_length (M g r₀ h : ℕ) :
    g + span M g r₀ h ≤ length M g r₀ (h + 1) := le_max_right _ _

/-- The key padding estimate: an entire child block occupies no more than twice
its incoming window length, independently of the size of the complete tree. -/
theorem childSpan_le_twice_length (M g r₀ h : ℕ) :
    childSpan M g r₀ h ≤ 2 * length M g r₀ (h + 1) := by
  have hp := gap_add_span_le_length M g r₀ h
  dsimp [childSpan]
  split_ifs <;> omega

end Problem310.WindowRecursion

end OAI


