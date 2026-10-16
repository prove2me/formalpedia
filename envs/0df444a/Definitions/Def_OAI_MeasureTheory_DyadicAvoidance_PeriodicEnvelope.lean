-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicEnvelope
-- name    : OAI_MeasureTheory_DyadicAvoidance_PeriodicEnvelope
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:36:00.883745+00:00
-- url     : https://prove2.me/theorems/2007eb2b-b9b3-48d8-89c1-dca15522ae7e
-- title:
--   Integer periodization $U+\mathbb{Z}$ of a subset of the real line
-- statement:
--   For a set $U\subseteq\mathbb{R}$, its integer periodization is
--   $$U+\mathbb{Z}=\bigcup_{k\in\mathbb{Z}}\{x\in\mathbb{R}: x+k\in U\}=\{u+m: u\in U,\ m\in\mathbb{Z}\},$$
--   the union of all integer translates of $U$. It contains $U$ (take $k=0$) and is $1$-periodic, that is, $x+1\in U+\mathbb{Z}$ if and only if $x\in U+\mathbb{Z}$. It is the smallest $1$-periodic subset of $\mathbb{R}$ containing $U$, and it is open whenever $U$ is open.
--
--   Periodization turns a set of controlled measure into a $1$-periodic set without increasing the measure seen in one period: for measurable $U$, the Lebesgue measure of $(U+\mathbb{Z})\cap[0,1]$ is at most the Lebesgue measure of $U$ (a companion estimate). In the construction of a compact set avoiding the affine copies $\{x+s\,2^{-n}:n\ge1\}$, $s\neq0$, of the dyadic sequence, this is how a $1$-periodic set is enlarged to an open $1$-periodic set whose density per period exceeds the original one by an arbitrarily small amount.
--
--   **Formalization Note** `integerPeriodize U` is defined as `⋃ k : ℤ, (fun x => x + k) ⁻¹' U`, the union over $k\in\mathbb{Z}$ of the preimages of $U$ under the translations $x\mapsto x+k$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/PeriodicEnvelope.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/PeriodicEnvelope.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace Problem310.Aux
open Set MeasureTheory

/-- Integer-periodization of a subset of the line. -/
def integerPeriodize (U : Set ℝ) : Set ℝ :=
  ⋃ k : ℤ, (fun x : ℝ => x + (k : ℝ)) ⁻¹' U

end Problem310.Aux

end

end OAI


