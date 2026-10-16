-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
-- name    : OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:11:13.39024+00:00
-- url     : https://prove2.me/theorems/da7370e0-73c3-4166-a68a-d9d740a38e14
-- title:
--   The set selected by an address map and a table of Boolean labels
-- statement:
--   Let $A$ and $K$ be sets and let $\operatorname{addr} : A \times \mathbb{R} \to K$ be an address map, assigning to each $a \in A$ and each point $x \in \mathbb{R}$ a label coordinate $\operatorname{addr}(a,x) \in K$. Boolean values are written $0$ (false) and $1$ (true). For an outcome $z = (a, \tau)$ consisting of $a \in A$ and a label table $\tau : K \to \{0,1\}$, the *selected set* is
--   $$
--   \Sigma(z) = \big\{ x \in \mathbb{R} : \tau\big(\operatorname{addr}(a,x)\big) = 1 \big\}.
--   $$
--   Thus the first component of the outcome decides, at every point $x$, which label is consulted, and the label table decides whether $x$ belongs to the set.
--
--   This abstraction underlies the first-moment computation of the random set in the dyadic avoidance construction, where $a$ is the selector table and $\operatorname{addr}(a,x)$ is the terminal coordinate reached by routing $x$. When the labels are independent with a common law and the label table is independent of $a$, each fixed point lies in $\Sigma(z)$ with the success probability of a single label, even though the consulted coordinate depends on $a$; integrating over $[0,1]$ then gives the expected density.
--
--   **Formalization Note** The outcome is an element of the product type `A × (K → Bool)`, and no structure on $A$, $K$ or the address map is required by the definition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/RandomSetDensity.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/RandomSetDensity.lean by skeleton subtraction
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

namespace OAI

universe u_A u_K

noncomputable section

open MeasureTheory

namespace Problem310.RandomSetDensity

/-- A selector outcome chooses the terminal address read at each point. -/
def selectedSet {A : Type u_A} {K : Type u_K} (addr : A → ℝ → K) (z : A × (K → Bool)) : Set ℝ :=
  {x | z.2 (addr z.1 x) = true}

end Problem310.RandomSetDensity

end

end OAI


