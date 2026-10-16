-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
-- name    : OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:15:18.874864+00:00
-- url     : https://prove2.me/theorems/c6c91bf1-eba3-4662-bd23-d951d98462e2
-- title:
--   The routed selector choice coincides with the centre choice
-- statement:
--   Fix $M, d \in \mathbb{N}$, selector resolutions $b$ (a natural number $b(P,i)$ for every node $P$, i.e. word over $\{0,\dots,M\}$ of length less than $d$, and every $i \in \{0,\dots,M-1\}$), and a selector table $\omega$, a $\{0,1\}$-valued function on the coordinates $((P,i),j)$ with $0 \le j < 2^{b(P,i)+2}$. For a word $P$ and $x \in \mathbb{R}$ let $s_\omega(P,i,x) = \omega((P,i), \lfloor 2^{b(P,i)+2}\{x\} \rfloor)$ when $|P| < d$ and $0$ otherwise, where $\{x\} = x - \lfloor x \rfloor$, and let $\operatorname{choose}(S)$ be the least $i < M$ with $S(i) = 1$, or the default child $M$ if there is none.
--
--   The file records, as a simplification rule, that the two names given to the first-success choice in different parts of the construction agree: for every table $\omega$, word $P$ and point $x$,
--   $$
--   \operatorname{sc}_\omega(P, x) = c_x(P, \omega) = \operatorname{choose}\big(i \mapsto s_\omega(P,i,x)\big).
--   $$
--   Here $\operatorname{sc}_\omega(P,x)$ is the selector choice used to route points into the random set, with the table fixed and the point $x$ as the routing parameter, and $c_x(P,\omega)$ is the centre choice used in the analysis at a fixed centre $x$, with the table as the parameter.
--
--   The identity holds by definition. It lets statements proved about routes of the random set be read as statements about centre routes and conversely, for instance when identifying the event that a point's route avoids the default child with the corresponding centre event.
--
--   **Formalization Note** The statement is `selectorChoice b ω P x = centerChoice b x P ω`, proved by `rfl` and tagged `@[simp]`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/RoutedExposure.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/RoutedExposure.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace Problem310.RoutedExposure
open FiniteTableModel RoutingPath CenterRouteExposure RoutedSetDensity

@[simp] theorem selectorChoice_eq_centerChoice {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (ω : SelectorTable b)
    (P : List (Child M)) (x : ℝ) :
    selectorChoice b ω P x = centerChoice b x P ω := rfl

end Problem310.RoutedExposure

end

end OAI


