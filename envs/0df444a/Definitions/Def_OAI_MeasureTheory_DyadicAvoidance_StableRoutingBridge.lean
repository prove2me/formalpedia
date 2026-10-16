-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_StableRoutingBridge
-- name    : OAI_MeasureTheory_DyadicAvoidance_StableRoutingBridge
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:24:21.453005+00:00
-- url     : https://prove2.me/theorems/b846dc48-c890-4198-a341-bf17bf9a2701
-- title:
--   Ordered first-success routing driven by spatial selector values
-- statement:
--   Fix $M \in \mathbb{N}$ and a parameter set $X$ (in applications $X = \mathbb{R}$, the points being routed). Children are $0,1,\dots,M$, the letter $M$ being the default child. Let $S$ be a family of selector values, assigning to each word $P$ over $\{0,\dots,M\}$, each selector index $i \in \{0,\dots,M-1\}$ and each $x \in X$ a value $S(P,i,x) \in \{0,1\}$, where $1$ means success.
--
--   The *ordered routing choice* associated with $S$ is
--   $$
--   \operatorname{sel}_S(P,x) = \min\Big( \big\{ i \in \{0,\dots,M-1\} : S(P,i,x) = 1 \big\} \cup \{M\} \Big),
--   $$
--   the first successful selector at $P$ for the parameter $x$, or the default child $M$ if no selector succeeds.
--
--   This choice rule is the abstract interface for stability arguments about routes. Comparing the routes of two points $x$ and $y$ then reduces to comparing the selector values $S(P,i,x)$ and $S(P,i,y)$ at the nodes actually visited: a nondefault decision is unchanged as soon as the selectors up to and including the chosen one agree, while later siblings and nodes off the path play no role. When $S$ is given by the selector values of a table read at points of $\mathbb{R}$, this choice is exactly the selector choice of the random router.
--
--   **Formalization Note** The choice is `OrderedRouting.chooseChild (fun i => S P i x)` with values in `Fin (M + 1)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/StableRoutingBridge.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/StableRoutingBridge.lean by skeleton subtraction
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

namespace OAI

universe u_X

noncomputable section

namespace Problem310.StableRouting

open OrderedRouting RoutingPath

variable {M : ℕ} {X : Type u_X}

/-- Ordered routing associated to the spatial selector values. -/
def select (S : List (Fin (M + 1)) → Fin M → X → Bool)
    (P : List (Fin (M + 1))) (x : X) : Fin (M + 1) :=
  chooseChild (fun i => S P i x)

end Problem310.StableRouting

end

end OAI


