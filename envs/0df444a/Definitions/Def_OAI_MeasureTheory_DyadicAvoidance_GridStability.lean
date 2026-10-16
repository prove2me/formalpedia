-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridStability
-- name    : OAI_MeasureTheory_DyadicAvoidance_GridStability
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:44:14.799432+00:00
-- url     : https://prove2.me/theorems/74b8741c-7398-4a36-90ed-2a5dbb2aee5e
-- title:
--   Stable centers: no crossing of the grid $2^{-(b_i+2)}\mathbb{Z}$ within $(x,x+2^{1-a_i}]$
-- statement:
--   Let $\iota$ be an index set and $a,b:\iota\to\mathbb{N}$. For $q\in\mathbb{N}$ and $\delta\in\mathbb{R}$ let $\mathrm{Bad}(q,\delta)=\bigcup_{k\in\mathbb{Z}}[k/q-\delta,\,k/q)$; for $q\ge1$ this is the set of centers $x$ for which the interval $(x,x+\delta]$ contains a point of the grid $q^{-1}\mathbb{Z}$. The set of simultaneously stable centers is
--   $$G(a,b)=\mathbb{R}\setminus\bigcup_{i\in\iota}\mathrm{Bad}\big(2^{b_i+2},\ 2\cdot2^{-a_i}\big).$$
--   Equivalently, $x\in G(a,b)$ if and only if for every $i\in\iota$ the interval $(x,\,x+2^{1-a_i}]$ contains no number of the form $k\,2^{-(b_i+2)}$ with $k\in\mathbb{Z}$.
--
--   Each index $i$ stands for a pair consisting of an earlier grid of resolution $b_i$, read through the key $\lfloor 2^{b_i+2}\{x\}\rfloor$ with $\{x\}=x-\lfloor x\rfloor$, and a later window of dyadic indices starting at $a_i$. For $n\ge a_i$ and $t\in[1,2]$ the displacement $t\,2^{-n}$ lies in $(0,2^{1-a_i}]$, so for a stable center $x$ the point $x+t\,2^{-n}$ stays in the same cell of the earlier grid as $x$ (a companion lemma). In the construction of a compact set avoiding the affine copies $\{x+s\,2^{-n}:n\ge1\}$, $s\neq0$, of the dyadic sequence, this guarantees that trial points used in later windows reproduce the routing decisions made at the center at all earlier resolutions, while the unstable centers have small measure per period.
--
--   **Formalization Note** `gridStableCenters a b` is the complement of `⋃ i, gridBadCenters (2 ^ (b i + 2)) (2 * (2⁻¹) ^ (a i))`. The index type `ι` is arbitrary in the definition; finiteness is assumed only in the results that bound its measure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/GridStability.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/GridStability.lean by skeleton subtraction
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

namespace OAI

universe u_ι

noncomputable section
namespace Problem310
open MeasureTheory Set

/-- Simultaneous stable centers for a finite list of earlier-grid/later-window pairs. -/
def gridStableCenters {ι : Type u_ι} (a b : ι → ℕ) : Set ℝ :=
  (⋃ i, gridBadCenters ((2 : ℕ) ^ (b i + 2)) (2 * ((2 : ℝ)⁻¹) ^ (a i)))ᶜ

end Problem310

end

end OAI


