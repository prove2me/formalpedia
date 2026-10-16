-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
-- name    : OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:04:36.646985+00:00
-- url     : https://prove2.me/theorems/6375fcd1-c596-49e4-9877-90f815e8ef00
-- title:
--   Exceptional centres: points at which a scaled copy of a sequence misses a set
-- statement:
--   Let $B \subseteq \mathbb{R}$ be a set, $N \subseteq \mathbb{N}$ a set of admissible indices, and $a = (a_n)_{n \in \mathbb{N}}$ a sequence of real numbers. The set of *exceptional centres* of $B$ with respect to $N$ and $a$ is
--   $$
--   \operatorname{Exc}(B,N,a) = \big\{ x \in \mathbb{R} : \exists\, t \in [1,2] \ \ \forall n \in N, \ \ x + t\,a_n \notin B \big\}.
--   $$
--   Thus $x$ is exceptional if, for some normalized scale $t$ in the closed interval $[1,2]$, the whole scaled copy $\{x + t\,a_n : n \in N\}$ of the sequence placed at $x$ misses $B$.
--
--   In the dyadic avoidance construction one takes $a_n = 2^{-n}$ and $N = \{n \in \mathbb{N} : n \ge 1\}$. A set $H$ meets every copy $\{x + t\,2^{-n} : n \ge 1\}$ with $x \in \mathbb{R}$ and $t \in [1,2]$ exactly when $\operatorname{Exc}(H,N,a) = \varnothing$. The construction produces a random one-periodic set $B$ for which most centres are exceptional only with small probability, and then removes the remaining exceptional centres by adding to $B$ an open one-periodic neighbourhood of $\operatorname{Exc}(B,N,a)$ of nearly the same measure.
--
--   **Formalization Note** The interval is `Set.Icc (1 : ℝ) 2`; no assumption on $B$, $N$ or $a$ is built into the definition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/ExceptionalCenters.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/ExceptionalCenters.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open Set Filter Topology

namespace Problem310.Auxiliary

section

/-- Centers at which some normalized scale avoids all the selected tests. -/
def exceptionalCenters (B : Set ℝ) (N : Set ℕ) (a : ℕ → ℝ) : Set ℝ :=
  {x | ∃ t ∈ Icc (1 : ℝ) 2, ∀ n ∈ N, x + t * a n ∉ B}

open Set Filter Topology MeasureTheory Metric

end

open Set Filter Topology MeasureTheory

end Problem310.Auxiliary

end

end OAI


