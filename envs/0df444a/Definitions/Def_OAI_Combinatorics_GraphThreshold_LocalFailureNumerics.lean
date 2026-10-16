-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_LocalFailureNumerics
-- name    : OAI_Combinatorics_GraphThreshold_LocalFailureNumerics
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:20:32.247079+00:00
-- url     : https://prove2.me/theorems/c81792cf-f4b6-4a62-a892-b0252b91531d
-- title:
--   Upper binomial tail $\sum_{m/2<r\le m}\binom{m}{r}q^{r}$
-- statement:
--   For $m\in\mathbb{N}$ and $q\in\mathbb{R}$, the large-intersection tail is
--
--   $$T_m(q)=\sum_{\substack{0\le r\le m\\ 2r>m}}\binom{m}{r}\,q^{r},$$
--
--   the part of the binomial expansion $(1+q)^m=\sum_{r=0}^{m}\binom{m}{r}q^r$ consisting of the terms with $r>m/2$.
--
--   The term $\binom{m}{r}q^r$ counts the $r$-element subsets of an $m$-element set, each weighted by $q^r$. In the resampling step of the threshold argument this sum bounds the contribution of random sets that meet a fixed set of at most $m$ elements in more than $m/2$ of them, where $q$ combines the spread parameter of the random set with a weight per intersected element. When $q$ is very small (for example $0\le q\le e^{-50}$), $T_m(q)$ is exponentially small in $m$, which is how such large intersections are shown to be rare.
--
--   **Formalization Note** The definition is `largeIntersectionTail m q`, a real sum over `range (m + 1)` in which the term for $r$ is `(m.choose r : ℝ) * q ^ r` if `m < 2 * r` and $0$ otherwise.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/LocalFailureNumerics.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/LocalFailureNumerics.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SecondKahnKalai mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Monotone
import Definitions.Def_SecondKahnKalai
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_EmbeddingExtension
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphSupport
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Basic
import Definitions.Def_OAI_Combinatorics_GraphThreshold_FiniteProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CopyOrbits
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphExpectedCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTree

namespace OAI

noncomputable section

open Finset

namespace LeanBlast.SecondKahnKalai

/-- The finite binomial upper tail used by the resampling argument. -/
def largeIntersectionTail (m : ℕ) (q : ℝ) : ℝ :=
  ∑ r ∈ range (m + 1), if m < 2 * r then (m.choose r : ℝ) * q ^ r else 0

end LeanBlast.SecondKahnKalai

end

end OAI


