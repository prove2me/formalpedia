-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowSpanSum
-- name    : OAI_MeasureTheory_DyadicAvoidance_WindowSpanSum
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:59:47.655425+00:00
-- url     : https://prove2.me/theorems/045335c2-ba8e-4576-b07d-defee0240d94
-- title:
--   Preorder lists of window lengths and their gap-padded sums
-- statement:
--   This file computes the total extent of a family of windows laid out in depth-first preorder along a complete tree, with a gap after every window. Fix natural numbers $M$ (the number of children of each node), $g$ (the gap) and $r_0$ (a minimum window length). The window recursion defines the span $\sigma(h)$ of a complete subtree of height $h$, the length $\ell(h)$ of the window on an edge whose upper endpoint has height $h$, and the span $c(h)$ of one edge together with the subtree below it:
--   $$\ell(0)=r_0,\qquad\ell(h+1)=\max\bigl(r_0,\ g+\sigma(h)\bigr),\qquad c(h)=\begin{cases}\ell(1),&h=0,\\ \ell(h+1)+g+\sigma(h),&h\ge1,\end{cases}$$
--   $$\sigma(0)=0,\qquad\sigma(h+1)=M\,c(h)+(M-1)\,g,$$
--   where $M-1$ is truncated at $0$.
--
--   1. **Preorder length list.** $\Lambda(0)$ is the empty list, and $\Lambda(h+1)$ is the concatenation of $M$ copies of the list $\bigl(\ell(h+1),\Lambda(h)\bigr)$, i.e. of the number $\ell(h+1)$ followed by the entries of $\Lambda(h)$. It lists the window lengths of all edges of the complete $M$-ary tree of height $h+1$ in depth-first preorder, each edge receiving the value of $\ell$ at the height of its upper endpoint.
--
--   2. **Padded sum.** For a list $L=(x_1,\dots,x_n)$ of natural numbers,
--   $$\Sigma_g(L)=\sum_{k=1}^{n}(x_k+g),$$
--   which charges one gap after every entry, including the last one.
--
--   The file proves that $\Sigma_g$ vanishes on the empty list, satisfies $\Sigma_g(x,L)=x+g+\Sigma_g(L)$, is additive under concatenation, and gets multiplied by $M$ when $M$ copies of a list are concatenated; that $(M-1)g+g=Mg$ when $M\ge1$; and that for $M\ge1$ and every $h\in\mathbb{N}$
--   $$\Sigma_g\bigl(\Lambda(h)\bigr)=\begin{cases}0,&h=0,\\ \sigma(h)+g,&h\ge1,\end{cases}\qquad\Sigma_g\bigl(\ell(h+1),\Lambda(h)\bigr)=c(h)+g\le2\,\ell(h+1)+g.$$
--
--   Thus the windows of one child block, an edge followed by its whole subtree, occupy exactly $c(h)$ positions plus one trailing gap, and this never exceeds twice the length of the edge's own window plus one gap, however large the tree is. This is the padding budget that keeps all windows below an edge close to that edge's window.
--
--   **Formalization Note** The definitions are `preorderLengths` and `paddedSum`; $\sigma$, $\ell$ and $c$ are `WindowRecursion.span`, `WindowRecursion.length` and `WindowRecursion.childSpan`, and the final inequality rests on `WindowRecursion.childSpan_le_twice_length`. The hypothesis $M\ge1$ is needed in the identities because Lean's truncated subtraction gives $(M-1)g=0$ for $M=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/WindowSpanSum.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/WindowSpanSum.lean by skeleton subtraction
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

namespace OAI

namespace Problem310.WindowSpanSum

open WindowRecursion

/-- The window lengths in edge preorder; the first length is that of the
incoming edge, followed by its complete descendant block. -/
def preorderLengths (M g r₀ : ℕ) : ℕ → List ℕ
  | 0 => []
  | h + 1 => (List.replicate M
      (WindowRecursion.length M g r₀ (h + 1) :: preorderLengths M g r₀ h)).flatten

/-- Charge a gap after every entry, including the final entry. -/
def paddedSum (g : ℕ) (L : List ℕ) : ℕ := (L.map (fun r => r + g)).sum

@[simp] theorem paddedSum_nil (g : ℕ) : paddedSum g [] = 0 := rfl

@[simp] theorem paddedSum_cons (g r : ℕ) (L : List ℕ) :
    paddedSum g (r :: L) = r + g + paddedSum g L := rfl

@[simp] theorem paddedSum_append (g : ℕ) (L K : List ℕ) :
    paddedSum g (L ++ K) = paddedSum g L + paddedSum g K := by
  simp [paddedSum]

@[simp] theorem paddedSum_flatten_replicate (g M : ℕ) (L : List ℕ) :
    paddedSum g (List.replicate M L).flatten = M * paddedSum g L := by
  induction M with
  | zero => simp [paddedSum]
  | succ M ih =>
      simp only [List.replicate_succ, List.flatten_cons, paddedSum_append, ih]
      ring

 theorem last_gap (M g : ℕ) (hM : 1 ≤ M) : (M - 1) * g + g = M * g := by
  simpa [Nat.add_mul] using congrArg (fun n => n * g) (Nat.sub_add_cancel hM)

/-- The exact recursive span is the preorder padded sum with the final gap removed. -/
theorem paddedSum_preorderLengths (M g r₀ h : ℕ) (hM : 1 ≤ M) :
    paddedSum g (preorderLengths M g r₀ h) =
      if h = 0 then 0 else span M g r₀ h + g := by
  induction h with
  | zero => rfl
  | succ h ih =>
      rw [preorderLengths, paddedSum_flatten_replicate, paddedSum_cons, ih]
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
      rw [span_succ]
      have hg := last_gap M g hM
      cases h with
      | zero =>
          simp only [ite_true, childSpan_zero, Nat.add_zero, Nat.zero_add]
          nlinarith
      | succ h =>
          simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
          rw [childSpan_succ]
          nlinarith

/-- A child block has its precise geometric span plus one terminal gap. -/
theorem paddedSum_childBlock (M g r₀ h : ℕ) (hM : 1 ≤ M) :
    paddedSum g (WindowRecursion.length M g r₀ (h + 1) :: preorderLengths M g r₀ h) =
      childSpan M g r₀ h + g := by
  rw [paddedSum_cons, paddedSum_preorderLengths M g r₀ h hM]
  cases h with
  | zero => simp
  | succ h => simp [childSpan_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- This is exactly the padded-length budget consumed by `WindowPlacement.block_padding`. -/
theorem childBlock_budget (M g r₀ h : ℕ) (hM : 1 ≤ M) :
    paddedSum g (WindowRecursion.length M g r₀ (h + 1) :: preorderLengths M g r₀ h) ≤
      2 * WindowRecursion.length M g r₀ (h + 1) + g := by
  rw [paddedSum_childBlock M g r₀ h hM]
  exact Nat.add_le_add_right (childSpan_le_twice_length M g r₀ h) g

end Problem310.WindowSpanSum

end OAI


