-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
-- name    : OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:17:42.743458+00:00
-- url     : https://prove2.me/theorems/7a1f2da4-3594-4b56-8902-b69565216801
-- title:
--   First-success child choice from selector bits indexed by tree addresses
-- statement:
--   Fix $M \in \mathbb{N}$. Children are $0,1,\dots,M$, the letter $M$ being the default child. An address is a pair $(P,j)$ of a word $P$ over $\{0,\dots,M\}$ (a node) and a selector index $j \in \{0,\dots,M-1\}$. Let $\Omega$ be a set and $S$ a family of Boolean selector bits, assigning to each address $a$ and each $\omega \in \Omega$ a value $S_a(\omega) \in \{0,1\}$, where $1$ means success.
--
--   The *canonical child choice* at a node $P$ under the outcome $\omega$ is the first-success choice among the selectors at $P$:
--   $$
--   c^{S}(P,\omega) = \min\Big( \big\{ j \in \{0,\dots,M-1\} : S_{(P,j)}(\omega) = 1 \big\} \cup \{M\} \Big) \in \{0,1,\dots,M\}.
--   $$
--   That is, the selectors at $P$ are inspected in the order $0, 1, \dots, M-1$, the first successful one is chosen, and the default child $M$ is chosen if none succeeds.
--
--   This is the routing rule of the abstract first-default model, in which selector bits are attached to all tree addresses of an arbitrary sample space. Routing from the root with this rule follows a prescribed nondefault path exactly on the corresponding path cylinder, which connects the cylinder computation of the probability of avoiding the default child to the actual route.
--
--   **Formalization Note** Addresses are `List (Fin (M + 1)) × Fin M` and the choice is `OrderedRouting.chooseChild (fun j => S (P, j) ω)`. The definition lives in the namespace `Problem310.FirstDefault`, so its name `centerChoice` is distinct from the centre choice of the concrete table model.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/FirstDefaultSelection.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/FirstDefaultSelection.lean by skeleton subtraction
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

namespace OAI

universe u_Ω u_ι u_X u_Y

noncomputable section

namespace Problem310.FirstDefault

/-- Canonical child choice from a family of selector bits at tree addresses. -/
def centerChoice {M : ℕ} {Ω : Type u_Ω} (S : Address M → Ω → Bool)
    (P : List (Fin (M + 1))) (ω : Ω) : Fin (M + 1) :=
  OrderedRouting.chooseChild (fun j => S (P, j) ω)

end Problem310.FirstDefault

end

end OAI


