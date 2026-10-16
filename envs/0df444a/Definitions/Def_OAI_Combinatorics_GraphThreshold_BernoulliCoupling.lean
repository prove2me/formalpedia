-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_BernoulliCoupling
-- name    : OAI_Combinatorics_GraphThreshold_BernoulliCoupling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:24:16.075609+00:00
-- url     : https://prove2.me/theorems/746b48c1-87c5-42f8-b411-a276e3c58c2a
-- title:
--   Bernoulli expectation of a constant function
-- statement:
--   Let $X$ be a finite set. For $p\in\mathbb{R}$, the Bernoulli product weight of a subset $W\subseteq X$ is $\mu_p(W)=\prod_{x\in X}w_x$, where $w_x=p$ if $x\in W$ and $w_x=1-p$ if $x\notin W$; for a real function $f$ on subsets of $X$, its Bernoulli expectation is $\mathbb{E}_p[f]=\sum_{W\subseteq X}\mu_p(W)\,f(W)$. The file records that for every $p\in\mathbb{R}$ and every constant $c\in\mathbb{R}$,
--
--   $$\mathbb{E}_p[c]=\sum_{W\subseteq X}\mu_p(W)\,c=c .$$
--
--   Equivalently, the weights $\mu_p(W)$ sum to $1$ for every real $p$, not only for $0\le p\le 1$. For $0\le p\le 1$, $\mathbb{E}_p$ is the expectation with respect to the $p$-random subset of $X$, for instance the edge set of the random graph $G(n,p)$, and the identity is the basic normalisation used when constants are pulled out of such expectations.
--
--   **Formalization Note** The statement is the simp lemma `bernoulliExpectation_const`, for a `Fintype` $X$ with decidable equality.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/BernoulliCoupling.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/BernoulliCoupling.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

variable {X : Type*} [Fintype X] [DecidableEq X]

@[simp] theorem bernoulliExpectation_const (p c : ℝ) :
    bernoulliExpectation p (fun _ : Finset X => c) = c := by
  rw [bernoulliExpectation, ← Finset.sum_mul, bernoulliWeight_sum, one_mul]

end LeanBlast.SecondKahnKalai

end

end OAI


