-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowExceptionalTransfer
-- name    : OAI_MeasureTheory_DyadicAvoidance_WindowExceptionalTransfer
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:27:00.592421+00:00
-- url     : https://prove2.me/theorems/76615f93-3175-441e-82c0-56b0918a0b77
-- title:
--   Local hit trials and scale stability of selectors in the window table model
-- statement:
--   Fix $M, d, g, r_0 \in \mathbb{N}$ and window data $W$ for a tree with $M+1$ children per node (child $M$ being the default), depth $d$, gap $g$ and threshold $r_0$; $W$ assigns to each word $P$ over $\{0,\dots,M\}$ a window $\{a_W(P), \dots, b_W(P)\}$ of scale exponents, with start $a_W(P)$ and end $b_W(P)$ in $\mathbb{N}$. Nodes are words $U$ with $|U| < d$, leaves are words of length $d$, and $U\,i$ is $U$ followed by $i$. For $n \in \mathbb{N}$ and $y \in \mathbb{R}$ let $\kappa_n(y) = \lfloor 2^{n+2}\{y\} \rfloor$ be the dyadic key, where $\{y\} = y - \lfloor y \rfloor$. A selector table $\omega_S$ is a $\{0,1\}$-valued function on the coordinates $((U,i),j)$ with $0 \le j < 2^{b_W(U\,i)+2}$, and a terminal table $\omega_T$ is a $\{0,1\}$-valued function on the coordinates $(L,j)$ with $0 \le j < 2^{b_W(L)+2}$. Selector values are $s_{\omega_S}(P,i,y) = \omega_S((P,i), \kappa_{b_W(P\,i)}(y))$ for $|P| < d$ and $0$ for longer words, and $\operatorname{sc}_{\omega_S}(P,y)$ is the first-success choice (least $i < M$ with $s_{\omega_S}(P,i,y) = 1$, or $M$).
--
--   1. **Depth bookkeeping.** For every node $U$ and $i < M$, $|U\,i| + \big(d - (|U|+1)\big) = d$.
--
--   2. **Local trial.** For a node $U$, an outcome $\omega = (\omega_S,\omega_T)$, an index $i < M$ and a point $y$, let $L$ be the leaf reached by routing $y$ with the choice rule $\operatorname{sc}_{\omega_S}$ for $d - |U| - 1$ steps starting from the node $U\,i$. The local trial succeeds when
--   $$
--   Q_{U,i}(\omega, y) = 1 \iff \omega_S\big((U,i),\ \kappa_{b_W(U\,i)}(y)\big) = 1 \ \text{ and } \ \omega_T\big(L,\ \kappa_{b_W(L)}(y)\big) = 1,
--   $$
--   i.e. the selector of child $i$ at $U$ succeeds at $y$, and the terminal label of the leaf reached from $U\,i$ is $1$ at $y$.
--
--   3. **Stability at a centre.** A point $x \in \mathbb{R}$ is stable for $W$ if for every node $P$, every $i < M$, every $n \in \mathbb{N}$ with $b_W(P\,i) + g < n$, every $t \in [1,2]$ and every selector table $\omega_S$,
--   $$
--   s_{\omega_S}(P, i, x) = s_{\omega_S}\big(P, i, x + t\,2^{-n}\big).
--   $$
--   Since this is required for every table, it amounts to $x$ and $x + t\,2^{-n}$ having the same dyadic key at resolution $b_W(P\,i)$ for all such $P, i, n, t$.
--
--   Stability says that moving the centre by $t\,2^{-n}$ at any scale exponent $n$ lying more than $g$ beyond the window end of the edge $P\,i$ does not change the selector of child $i$ at $P$. It is the geometric input of the local analysis: if the centre route of $x$ first takes the default child at the node $U$, $x$ is stable, and $n \ge a_W(U\,i)$, then the shifted point $y = x + t\,2^{-n}$ follows the centre route down to $U$ and rejects the children $j < i$ there, so a successful local trial $Q_{U,i}(\omega, y)$ places $y$ in the routed random set. This is how the event that a centre is exceptional is transferred to the simultaneous failure of finitely many local trials.
--
--   **Formalization Note** The local trial is the Boolean conjunction (`&&`) of the two table reads, and the leaf is `FiniteLocalPredicate.localLeaf` with $r = d - (|U| + 1)$; the lemma `local_depth` supplies its depth hypothesis, where truncated subtraction is harmless because $|U| < d$. The shifted point is written `x + t * (2 : ℝ)⁻¹ ^ n`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/WindowExceptionalTransfer.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/WindowExceptionalTransfer.lean by skeleton subtraction
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

namespace OAI

noncomputable section
namespace Problem310.WindowExceptionalTransfer

open FiniteTableModel RoutedSetDensity RoutingPath FiniteLocalPredicate CenterRouteExposure

variable {M d g r₀ : ℕ}

lemma local_depth (U : Node M d) (i : Fin M) :
    (U.val ++ [i.castSucc]).length + (d - (U.val.length + 1)) = d := by
  have h := U.property
  simp only [List.length_append, List.length_singleton]
  omega

/-- The actual local Boolean test, using the canonical tables and subtree router. -/
def localQ (W : WindowData (M + 1) d g r₀) (U : Node M d)
    (ω : SelectorTable (selectorEndpoints W) × TerminalTable (terminalEndpoints W))
    (i : Fin M) (y : ℝ) : Bool :=
  ω.1 (selectorAddress (selectorEndpoints W) U i y) &&
    ω.2 (terminalAddress (terminalEndpoints W)
      (localLeaf (selectorChoice (selectorEndpoints W) ω.1)
        (d - (U.val.length + 1)) (U.val ++ [i.castSucc]) (local_depth U i) y) y)

/-- Stability in precisely the selector-value form supplied by the canonical
window stability construction. -/
def StableAt (W : WindowData (M + 1) d g r₀) (x : ℝ) : Prop :=
  ∀ (P : Node M d) (i : Fin M) (n : ℕ),
    W.b (P.val ++ [i.castSucc]) + g < n →
    ∀ t ∈ Set.Icc (1 : ℝ) 2, ∀ ω : SelectorTable (selectorEndpoints W),
      selectorValue (selectorEndpoints W) ω P.val i x =
        selectorValue (selectorEndpoints W) ω P.val i (x + t * (2 : ℝ)⁻¹ ^ n)

end Problem310.WindowExceptionalTransfer

end

end OAI


