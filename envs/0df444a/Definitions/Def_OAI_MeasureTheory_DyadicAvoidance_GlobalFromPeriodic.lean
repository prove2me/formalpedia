-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GlobalFromPeriodic
-- name    : OAI_MeasureTheory_DyadicAvoidance_GlobalFromPeriodic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:39:09.44196+00:00
-- url     : https://prove2.me/theorems/d28c14e3-20a6-43e4-9d14-95054b45db48
-- title:
--   Signed dyadic union $\bigcup_j\bigl(2^{-j}H_j\cup(-2^{-j}H_j)\bigr)$ of a sequence of sets
-- statement:
--   Let $H=(H_j)_{j\in\mathbb{N}}$ be a sequence of subsets of $\mathbb{R}$, indexed by $j=0,1,2,\dots$. Its signed dyadic union is the set
--   $$\mathcal{C}(H)=\bigcup_{j=0}^{\infty}\Big(\{x\in\mathbb{R}: 2^jx\in H_j\}\cup\{x\in\mathbb{R}: -2^jx\in H_j\}\Big)=\bigcup_{j=0}^{\infty}\Big(2^{-j}H_j\cup\big(-2^{-j}H_j\big)\Big).$$
--   Thus the $j$-th set is contracted by the factor $2^{-j}$ and also reflected through the origin, and $\mathcal{C}(H)$ is symmetric: $x\in\mathcal{C}(H)$ if and only if $-x\in\mathcal{C}(H)$.
--
--   This set is the passage from normalized scales to all scales in the construction of a compact set $E\subseteq[0,1]$ of measure close to $1$ that contains no affine copy $\{x+s\,2^{-n}:n\ge1\}$, $x\in\mathbb{R}$, $s\neq0$, of the dyadic sequence. A companion result shows that if each $H_j$ meets every normalized copy, i.e. for every $y\in\mathbb{R}$ and $t\in[1,2]$ some $n\ge1$ has $y+t\,2^{-n}\in H_j$, then $\mathcal{C}(H)$ meets every copy $\{x+s\,2^{-n}:n\ge1\}$ with $x\in\mathbb{R}$ and $s\neq0$. The avoiding set is then obtained by removing $\mathcal{C}(H)$ from $[0,1]$; when every $H_j$ is $1$-periodic, the Lebesgue measure of $\mathcal{C}(H)\cap[0,1]$ is at most $2\sum_j\lambda(H_j\cap[0,1])$, where $\lambda$ denotes Lebesgue measure.
--
--   **Formalization Note** `signedDyadicUnion H` is the union over `j : ℕ` (so $j=0$ is included) of `{x | 2 ^ j * x ∈ H j} ∪ {x | -(2 ^ j * x) ∈ H j}`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/GlobalFromPeriodic.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/GlobalFromPeriodic.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem310Support

/-- The paired pullbacks used to cover all signed scales. -/
def signedDyadicUnion (H : ℕ → Set ℝ) : Set ℝ :=
  ⋃ j : ℕ, ({x : ℝ | (2 : ℝ) ^ j * x ∈ H j} ∪
    {x : ℝ | -((2 : ℝ) ^ j * x) ∈ H j})

end Problem310Support

end

end OAI


