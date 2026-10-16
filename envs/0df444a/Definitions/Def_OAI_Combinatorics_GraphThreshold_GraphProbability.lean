-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability
-- name    : OAI_Combinatorics_GraphThreshold_GraphProbability
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:09:34.43044+00:00
-- url     : https://prove2.me/theorems/595cded3-eac9-48e5-81b6-ad64a97f6364
-- title:
--   Bernoulli product weights, expectations and probabilities at $p=0$ and $p=1$
-- statement:
--   Let $X$ be a finite set and $p\in\mathbb{R}$. The **Bernoulli product weight** of a subset $W\subseteq X$ is
--
--   $$\mu_p(W)=\prod_{x\in X}\begin{cases}p, & x\in W,\\ 1-p, & x\notin W,\end{cases}$$
--
--   which, for $0\le p\le 1$, is the probability that the $p$-random subset of $X$ (each element kept independently with probability $p$) equals $W$. For a real function $f$ on subsets of $X$ and a property $P$ of subsets, write
--
--   $$\mathbb{E}_p[f]=\sum_{W\subseteq X}\mu_p(W)\,f(W),\qquad \mathbb{P}_p[P]=\sum_{W\subseteq X,\ P(W)}\mu_p(W).$$
--
--   The file evaluates these quantities at the endpoints $p=0$ and $p=1$:
--
--   1. $\mu_0(W)=1$ if $W=\emptyset$ and $\mu_0(W)=0$ otherwise; $\mu_1(W)=1$ if $W=X$ and $\mu_1(W)=0$ otherwise.
--   2. For every $f$: $\mathbb{E}_0[f]=f(\emptyset)$ and $\mathbb{E}_1[f]=f(X)$.
--   3. For every $P$: $\mathbb{P}_0[P]$ equals $1$ if $P(\emptyset)$ holds and $0$ otherwise, and $\mathbb{P}_1[P]$ equals $1$ if $P(X)$ holds and $0$ otherwise.
--
--   In words, the $0$-random subset is the empty set and the $1$-random subset is all of $X$, with certainty. These are the boundary cases of the parameter interval $[0,1]$ for the random graph $G(n,p)$, where $X$ is the set of possible edges, and they are convenient in monotonicity and threshold arguments.
--
--   **Formalization Note** $\mu_p$, $\mathbb{E}_p$ and $\mathbb{P}_p$ are `bernoulliWeight`, `bernoulliExpectation` and `bernoulliProbability`; they are defined for every real $p$, without the restriction $0\le p\le 1$, and $X$ is a `Fintype` with decidable equality. The file also contains a private copy `ite_eq_right` of the rewriting rule `if_neg`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/GraphProbability.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/GraphProbability.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

namespace LeanBlast.SecondKahnKalai

section BernoulliEndpoints

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem bernoulliWeight_zero (W : Finset X) :
    bernoulliWeight 0 W = if W = ∅ then 1 else 0 := by
  by_cases hW : W = ∅
  · subst W
    simp [bernoulliWeight]
  · rw [ite_eq_right hW]
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hW
    exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [hx])

theorem bernoulliWeight_one (W : Finset X) :
    bernoulliWeight 1 W = if W = Finset.univ then 1 else 0 := by
  by_cases hW : W = Finset.univ
  · subst W
    simp [bernoulliWeight]
  · rw [ite_eq_right hW]
    obtain ⟨x, hx⟩ : ∃ x : X, x ∉ W := by
      simpa [Finset.eq_univ_iff_forall] using hW
    exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [hx])

@[simp]
theorem bernoulliExpectation_zero (f : Finset X → ℝ) :
    bernoulliExpectation 0 f = f ∅ := by
  simp [bernoulliExpectation, bernoulliWeight_zero]

@[simp]
theorem bernoulliExpectation_one (f : Finset X → ℝ) :
    bernoulliExpectation 1 f = f Finset.univ := by
  simp [bernoulliExpectation, bernoulliWeight_one]

@[simp]
theorem bernoulliProbability_zero (P : Finset X → Prop) [DecidablePred P] :
    bernoulliProbability 0 P = if P ∅ then 1 else 0 := by
  classical
  unfold bernoulliProbability
  rw [Finset.sum_eq_single ∅]
  · simp [bernoulliWeight_zero]
  · intro W _ hW
    simp [bernoulliWeight_zero, hW]
  · simp

@[simp]
theorem bernoulliProbability_one (P : Finset X → Prop) [DecidablePred P] :
    bernoulliProbability 1 P = if P Finset.univ then 1 else 0 := by
  classical
  unfold bernoulliProbability
  rw [Finset.sum_eq_single Finset.univ]
  · simp [bernoulliWeight_one]
  · intro W _ hW
    simp [bernoulliWeight_one, hW]
  · simp

end BernoulliEndpoints

end LeanBlast.SecondKahnKalai

end

end OAI


