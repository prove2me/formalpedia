-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridMeasure
-- name    : OAI_MeasureTheory_DyadicAvoidance_GridMeasure
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:42:30.844723+00:00
-- url     : https://prove2.me/theorems/b3feb52c-12be-4df4-8637-43c8048296e6
-- title:
--   Centers whose forward displacement by at most $\delta$ crosses the grid $q^{-1}\mathbb{Z}$
-- statement:
--   Let $q$ be a positive integer and $\delta\in\mathbb{R}$. The set of bad (grid-crossing) centers for the grid $q^{-1}\mathbb{Z}$ and displacement length $\delta$ is
--   $$\mathrm{Bad}(q,\delta)=\bigcup_{k\in\mathbb{Z}}\Big[\frac{k}{q}-\delta,\ \frac{k}{q}\Big).$$
--   Since $k/q-\delta\le x<k/q$ is equivalent to $x<k/q\le x+\delta$, a real number $x$ belongs to $\mathrm{Bad}(q,\delta)$ exactly when the half-open interval $(x,x+\delta]$ contains a point of $q^{-1}\mathbb{Z}$, that is, when a forward displacement of $x$ by at most $\delta$ crosses a boundary of the half-open grid cells $[k/q,(k+1)/q)$. For $\delta\le0$ the set is empty.
--
--   Outside $\mathrm{Bad}(q,\delta)$, every point $x+u$ with $0<u\le\delta$ lies in the same grid cell as $x$, so grid keys at mesh $1/q$ are unchanged by such displacements. Companion results show that $\mathrm{Bad}(q,\delta)$ is $1$-periodic and that, for finitely many pairs $(q_i,\delta_i)$ with $q_i\ge1$ and $0\le\delta_i\le1/q_i$, the union of the sets $\mathrm{Bad}(q_i,\delta_i)$ meets $[0,1]$ in Lebesgue measure at most $\sum_iq_i\delta_i$. In the construction of a compact set avoiding the affine copies $\{x+s\,2^{-n}:n\ge1\}$, $s\neq0$, of the dyadic sequence, this is how the centers at which dyadic translations might disturb earlier grid keys are discarded at small cost.
--
--   **Formalization Note** `gridBadCenters q δ` takes `q : ℕ`, cast to a real number, and is the union over `k : ℤ` of `Ico (k / q - δ) (k / q)`. For `q = 0`, Lean's convention $k/0=0$ makes it the single interval $[-\delta,0)$; the statements that use it assume $q>0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/GridMeasure.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/GridMeasure.lean by skeleton subtraction
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

namespace OAI

universe u_ι

noncomputable section
namespace Problem310
open MeasureTheory Set

/-- Centers whose positive displacement of length `δ` crosses a boundary
of the periodic grid with `q` cells. -/
def gridBadCenters (q : ℕ) (δ : ℝ) : Set ℝ :=
  ⋃ k : ℤ, Ico ((k : ℝ) / q - δ) ((k : ℝ) / q)

end Problem310

end

end OAI


