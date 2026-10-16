-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteWindowAtom
-- name    : OAI_MeasureTheory_DyadicAvoidance_ConcreteWindowAtom
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:33:08.260981+00:00
-- url     : https://prove2.me/theorems/036fefbd-d635-4f50-a6f7-81b176e3f0d1
-- title:
--   Local miss event: all child-window tests fail on a center-exposure atom
-- statement:
--   Fix natural numbers $M,d,g,r_0$ and the complete ordered tree of depth $d$ in which every internal vertex has $M+1$ children labelled $0,\dots,M$, the label $M$ being the *default* child. Vertices are words over $\{0,\dots,M\}$ of length at most $d$: internal nodes are the words $P$ with $|P|<d$, leaves are the words of length $d$, and an edge is identified with the word of its lower endpoint. Let $W$ be window data for this tree with gap $g$ and threshold $r_0$; it assigns to every edge $e$ a window $\{a_e,\dots,b_e\}$ of consecutive integers whose length $r_h$ depends only on the height $h$ of the parent vertex. For $b\in\mathbb{N}$ and $y\in\mathbb{R}$ let $J_b(y)=\lfloor 2^{b+2}\{y\}\rfloor\in\{0,\dots,2^{b+2}-1\}$, where $\{y\}=y-\lfloor y\rfloor$.
--
--   The outcome space $\Omega$ consists of pairs $\omega=(\sigma,\tau)$ of Boolean tables: a *selector table* $\sigma_{Pi}:\{0,\dots,2^{b_{Pi}+2}-1\}\to\{0,1\}$ for every internal node $P$ and nondefault label $0\le i<M$, and a *terminal table* $\tau_L:\{0,\dots,2^{b_L+2}-1\}\to\{0,1\}$ for every leaf $L$. The selectors route a point $y$: at an internal node $Q$ go to the least child $i<M$ with $\sigma_{Qi}(J_{b_{Qi}}(y))=1$, or to the default child $M$ if there is none. For an internal node $U$, a label $0\le i<M$ and $y\in\mathbb{R}$, let $L^U_i(y)$ be the leaf reached by applying this rule starting from the vertex $Ui$, and define the local test
--   $$Q_{U,i}(y)=\sigma_{Ui}\big(J_{b_{Ui}}(y)\big)\wedge\tau_{L^U_i(y)}\big(J_{b_{L^U_i(y)}}(y)\big)\in\{0,1\}.$$
--
--   For an internal node $U$, reals $x,t$, and an exposure pattern $\xi$ assigning a bit $\xi(P,i)$ to every internal node $P$ and label $0\le i<M$, the local miss event is
--   $$\mathrm{Miss}_W(U,x,t,\xi)=\Big\{(\sigma,\tau)\in\Omega:\ \sigma_{Pi}\big(J_{b_{Pi}}(x)\big)=\xi(P,i)\ \text{for all }(P,i),\ \text{and}\ Q_{U,i}\big(x+t\,2^{-(a_{Ui}+k)}\big)=0\ \text{for all }0\le i<M,\ 0\le k<r\Big\},$$
--   where $r=r_{d-|U|}$ is the window length of the edges leaving $U$. The first condition says that the selector entries read at the center $x$ (one entry in every selector table) form the pattern $\xi$; the second says that each of the $Mr$ tests at the points $x+t\,2^{-n}$, with $n$ in the window of a nondefault child edge $Ui$, fails.
--
--   This event appears in the construction of a compact set avoiding all affine copies $\{x+s\,2^{-n}:n\ge1\}$, $s\neq0$, of the dyadic sequence. For a stable center $x$ whose path first takes the default child at $U$, a successful test $Q_{U,i}=1$ at a trial point certifies that this point lies in the random set, so $\mathrm{Miss}_W(U,x,t,\xi)$ is the failure event on one atom of the center exposure at one scale. A companion computation shows that, when the selector bits are independent fair coins, the terminal bits are independent Bernoulli($p$) variables and $1\le t\le2$, its probability equals $(1-p/2)^{Mr}$ times the probability of the atom.
--
--   **Formalization Note** The event is `localMiss W U x t ξ`, a subset of `SelectorTable (selectorEndpoints W) × TerminalTable (terminalEndpoints W)`. The center condition is `centerExposure (selectorEndpoints W) x ω.1 = ξ`, and $Q_{U,i}$ is `localQ W U ω i`, which uses the first-success router `selectorChoice` and the leaf `localLeaf` reached in $d-|U|-1$ steps from $Ui$. The trial index $a_{Ui}+k$ is `localIndex W U z` for $z=(i,k)$ in `LocalTrial W U`, and Lean writes $2^{-n}$ as $(2^{-1})^n$. The definition places no restriction on $U$, $x$, $t$ or $\xi$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/ConcreteWindowAtom.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/ConcreteWindowAtom.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Problem310.ConcreteWindowAtom

open FiniteTableModel RoutedSetDensity RoutingPath FiniteLocalPredicate
open CenterRouteExposure CenterFailureBound WindowExceptionalTransfer WindowTrialAddresses

variable {M d g r₀ : ℕ}

/-- The concrete center atom together with all child-window trial misses. -/
def localMiss (W : WindowData (M + 1) d g r₀) (U : Node M d)
    (x t : ℝ) (ξ : Node M d × Fin M → Bool) :
    Set (SelectorTable (selectorEndpoints W) × TerminalTable (terminalEndpoints W)) :=
  {ω | centerExposure (selectorEndpoints W) x ω.1 = ξ ∧
    ∀ z : LocalTrial W U, localQ W U ω z.1
      (x + t * (2 : ℝ)⁻¹ ^ localIndex W U z) = false}

end Problem310.ConcreteWindowAtom

end

end OAI


