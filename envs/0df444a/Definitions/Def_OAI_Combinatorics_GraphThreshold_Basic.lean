-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_Basic
-- name    : OAI_Combinatorics_GraphThreshold_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:12:40.578984+00:00
-- url     : https://prove2.me/theorems/ef07dc2d-bc2d-40c1-9697-4140899545d4
-- title:
--   Finite probability laws and $a$-spread random sets
-- statement:
--   1. **Finite law.** For a finite set $\Omega$, a finite law on $\Omega$ is a weight function $\mu:\Omega\to\mathbb{R}$ with $\mu(\omega)\ge 0$ for every $\omega\in\Omega$ and $\sum_{\omega\in\Omega}\mu(\omega)=1$; that is, a probability distribution on $\Omega$.
--
--   2. **Expectation.** For $f:\Omega\to\mathbb{R}$, $\mathbb{E}_\mu[f]=\sum_{\omega\in\Omega}\mu(\omega)\,f(\omega)$.
--
--   3. **Probability.** For a property $P$ of elements of $\Omega$, $\mu(P)=\sum_{\omega\in\Omega,\ P(\omega)}\mu(\omega)$.
--
--   4. **Positivity.** $\mu$ is positive if $\mu(\omega)>0$ for every $\omega\in\Omega$, i.e. it has full support.
--
--   5. **Spread.** Let $X$ be a set, let $B$ be a finite index set carrying a finite law $\mu$, let $A$ assign to each $b\in B$ a finite subset $A(b)\subseteq X$, and let $a\in\mathbb{R}$. The family $A$ is $a$-spread under $\mu$ if for every nonempty finite set $J\subseteq X$
--
--      $$\mu\bigl(\{b\in B:\ J\subseteq A(b)\}\bigr)\le a^{|J|} .$$
--
--      In probabilistic language: the random set $A(b)$ with $b$ drawn from $\mu$ contains any fixed nonempty set $J$ with probability at most $a^{|J|}$.
--
--   Finite laws provide an elementary probability framework (finite sums only, no measure theory) for the threshold argument for random graphs. Spread is the central hypothesis of that argument: a random set whose law is $a$-spread for small $a$ cannot concentrate on any fixed configuration, and spread families are the ones that a $p$-random set is shown to cover with good probability.
--
--   **Formalization Note** `FiniteLaw Ω` is a structure with fields `weight`, `nonneg` and `total`; the derived notions are `FiniteLaw.expectation`, `FiniteLaw.prob` (using classical decidability of $P$), `FiniteLaw.IsPositive` and `IsSpread μ A a`. The set $X$ need not be finite, only decidable equality is assumed, and the empty set is excluded from the spread condition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/Basic.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace LeanBlast.SecondKahnKalai

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

namespace FiniteLaw

def expectation {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω, μ.weight ω * f ω

def prob {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (P : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if P ω then μ.weight ω else 0

def IsPositive {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) : Prop :=
  ∀ ω, 0 < μ.weight ω

end FiniteLaw

def IsSpread {X B : Type*} [DecidableEq X] [Fintype B]
    (μ : FiniteLaw B) (A : B → Finset X) (a : ℝ) : Prop :=
  ∀ J : Finset X, J.Nonempty → μ.prob (fun b => J ⊆ A b) ≤ a ^ J.card

end LeanBlast.SecondKahnKalai

end

end OAI


