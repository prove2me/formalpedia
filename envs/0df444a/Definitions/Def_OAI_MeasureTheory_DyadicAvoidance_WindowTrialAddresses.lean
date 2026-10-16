-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTrialAddresses
-- name    : OAI_MeasureTheory_DyadicAvoidance_WindowTrialAddresses
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:32:12.279417+00:00
-- url     : https://prove2.me/theorems/190e3aa3-972c-4a75-a278-3d2738f24d64
-- title:
--   Child-window trials at a tree node and the selector entries they read
-- statement:
--   Fix natural numbers $M,d,g,r_0$ and consider the complete ordered tree of depth $d$ in which every internal vertex has $M+1$ children, labelled $0,1,\dots,M$; the label $M$ is the *default* child and $0,\dots,M-1$ are the *nondefault* children. Vertices are words $P$ over $\{0,\dots,M\}$ with $|P|\le d$; an *internal node* is a word with $|P|<d$, whose height is $d-|P|$; and the edge from $P$ to its child $i$ is identified with the word $Pi$. Let $W$ be window data for this tree with gap $g$ and threshold $r_0$. The only features used here are that $W$ assigns to every edge $e$ a window $\{a_e,a_e+1,\dots,b_e\}$ of consecutive integers whose length $b_e-a_e+1=r_h$ depends only on the height $h$ of the parent vertex. Every nondefault edge $Pi$ carries a selector table read at resolution $b_{Pi}$ through the key $J_b(y)=\lfloor 2^{b+2}\{y\}\rfloor$, where $\{y\}=y-\lfloor y\rfloor$. Fix an internal node $P$ and put $r=r_{d-|P|}$, the common window length of the edges leaving $P$.
--
--   1. **Local trials.** The local trial set at $P$ is $T_P=\{0,\dots,M-1\}\times\{0,\dots,r-1\}$, one block of $r$ trials for each nondefault child; it has exactly $M\,r_{d-|P|}$ elements.
--   2. **Local starts.** For $0\le i<M$, the local start of child $i$ is $a_{Pi}$, the first index of the window of the nondefault edge $Pi$.
--   3. **Local index.** Trial $(i,k)\in T_P$ uses the dyadic index $n_P(i,k)=a_{Pi}+k$. As $k$ runs through $0,\dots,r-1$, this runs through the window $\{a_{Pi},\dots,b_{Pi}\}$ of the edge $Pi$.
--   4. **Local selector address.** For a center $x\in\mathbb{R}$ and a scale $t\in\mathbb{R}$, trial $(i,k)$ reads the selector coordinate
--   $$\Big(Pi,\ J_{b_{Pi}}\big(x+t\,2^{-(a_{Pi}+k)}\big)\Big),$$
--   the entry of the selector table of the edge $Pi$ whose cell contains the trial point $x+t\,2^{-n_P(i,k)}$.
--
--   In the construction of a compact set avoiding all affine copies $\{x+s\,2^{-n}:n\ge1\}$, $s\neq0$, of the dyadic sequence, a random routing rule sends points down this tree. When the path of a center $x$ first takes a default child at a node $P$, membership is tested at the points $x+t\,2^{-n}$ with $n$ in the windows of the nondefault child edges of $P$. These definitions name those $Mr$ tests and the selector entries they consult. Companion results show that, for $1\le t\le2$, these entries are pairwise distinct and distinct from the entries read at the center $x$ itself, so the corresponding random bits are independent of the information exposed at the center.
--
--   **Formalization Note** `LocalTrial W P` is `WindowTrial M (W.r (d - P.val.length))`; `localStarts W P i = W.a (selectorEdge P i)` with `selectorEdge P i = P.val ++ [i.castSucc]`; `localIndex` is `windowTrialIndex (localStarts W P)`; and `localSelectorAddress W P x t z` is `selectorAddress (selectorEndpoints W) P z.1` evaluated at the trial point, an element of the sigma type `SelectorAddress (selectorEndpoints W)` whose table for the edge $Pi$ has resolution `W.b (selectorEdge P i)`. The window structure indexes lengths as `W.r (d + 1 - e.length)` for an edge word `e`, which equals $r_{d-|P|}$ for the edge $Pi$. The cardinality is `card_localTrial`, and Lean writes $2^{-n}$ as $(2^{-1})^n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/WindowTrialAddresses.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/WindowTrialAddresses.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace Problem310.WindowTrialAddresses

open FiniteTableModel TrialAddresses

variable {M d g r₀ : ℕ}

abbrev LocalTrial (W : WindowData (M + 1) d g r₀) (P : Node M d) :=
  WindowTrial M (W.r (d - P.val.length))

def localStarts (W : WindowData (M + 1) d g r₀) (P : Node M d) (i : Fin M) : ℕ :=
  W.a (selectorEdge P i)

def localIndex (W : WindowData (M + 1) d g r₀) (P : Node M d)
    (z : LocalTrial W P) : ℕ := windowTrialIndex (localStarts W P) z

@[simp] theorem card_localTrial (W : WindowData (M + 1) d g r₀) (P : Node M d) :
    Fintype.card (LocalTrial W P) = M * W.r (d - P.val.length) := by
  simp [LocalTrial]

/-- The actual finite-model selector coordinate read at one child-window trial. -/
def localSelectorAddress (W : WindowData (M + 1) d g r₀) (P : Node M d)
    (x t : ℝ) (z : LocalTrial W P) : SelectorAddress (selectorEndpoints W) :=
  selectorAddress (selectorEndpoints W) P z.1
    (x + t * ((2 : ℝ)⁻¹ ^ localIndex W P z))

end Problem310.WindowTrialAddresses

end

end OAI


