-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_ResamplingEvents
-- name    : OAI_Combinatorics_GraphThreshold_ResamplingEvents
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:31:01.873202+00:00
-- url     : https://prove2.me/theorems/af01fb77-a99d-41dd-a50e-26fe7d0d1f23
-- title:
--   Local success and failure events of a resampling transition
-- statement:
--   Let $X$ be a type with decidable equality, $B$ a finite index set, $\nu$ a finite law on $B$ (weights $\nu(b)\ge0$ summing to $1$), $(A_b)_{b\in B}$ finite labels $A_b\subseteq X$, $\rho$ a real parameter, $m$ a natural number (the capacity) and $W\subseteq X$ a finite set. As in the planted resampling transition, for a finite $Y\subseteq X$ put
--   $$Z(Y)=\sum_{b\in B:\ A_b\subseteq Y}\nu(b)\,\rho^{-|A_b|},$$
--   the normalizing density of the transition that, from a source index $c$, observes the set $W\cup A_c$ and then draws a target index $b$ with $A_b\subseteq W\cup A_c$.
--
--   1. **Local success.** For a source $c\in B$ and a target $b\in B$, the pair $(c,b)$ is a local success if the density at the observed set is not too small and the retained fragment fits into half the capacity:
--   $$\mathrm{Succ}(c,b)\iff e^{-10m}\le Z(W\cup A_c)\quad\text{and}\quad |A_b\setminus W|\le\lfloor m/2\rfloor .$$
--   2. **Local failure.** $\mathrm{Fail}(c,b)$ is the negation of $\mathrm{Succ}(c,b)$, that is, $Z(W\cup A_c)<e^{-10m}$ or $|A_b\setminus W|>\lfloor m/2\rfloor$.
--
--   These events classify one resampling step at a node of capacity $m$. On a success, the fragment $A_b\setminus W$ that replaces the planted label has at most half the capacity, so capacities halve from one round of reductions to the next; on a success the density cutoff also gives $1/Z(W\cup A_c)\le e^{10m}$, which is the bound used in the change-of-measure estimates for the reduction.
--
--   **Formalization Note** $\lfloor m/2\rfloor$ is natural-number division `m / 2`. The events are the propositions `LocalSuccess ν A ρ m W c b` and `LocalFailure ν A ρ m W c b`, with $Z$ given by `resamplingZ`; the power $\rho^{-|A_b|}$ uses Lean's inverse, so it is $0$ when $\rho=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/ResamplingEvents.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/ResamplingEvents.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_GraphThreshold_LocalFailureNumerics
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Predecessor
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphHierarchy
import Definitions.Def_OAI_Combinatorics_GraphThreshold_BernoulliCoupling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_AdaptiveTrials
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeFacts
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeTrim
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CapacityIteration
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Resampling

namespace OAI

/-! # Success and failure of a local resampling transition -/

noncomputable section

namespace LeanBlast.SecondKahnKalai

variable {X B : Type*} [DecidableEq X] [Fintype B]

/-- The denominator is large enough and the retained fragment fits in the
halved integral capacity. -/
def LocalSuccess (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ) (m : ℕ)
    (W : Finset X) (c b : B) : Prop :=
  Real.exp (-10 * (m : ℝ)) ≤ resamplingZ ν A ρ (W ∪ A c) ∧
    (A b \ W).card ≤ m / 2

/-- A local failure is the complement of the actual local success event. -/
def LocalFailure (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ) (m : ℕ)
    (W : Finset X) (c b : B) : Prop :=
  ¬ LocalSuccess ν A ρ m W c b

end LeanBlast.SecondKahnKalai

end

end OAI


