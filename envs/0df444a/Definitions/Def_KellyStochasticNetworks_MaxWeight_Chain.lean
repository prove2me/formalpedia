-- Prove2me | Definitions.Def_KellyStochasticNetworks_MaxWeight_Chain
-- name    : KellyStochasticNetworks_MaxWeight_Chain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:48:38.579678+00:00
-- url     : https://prove2.me/theorems/d0f6b88e-0078-4e07-b325-f6497885f8c8
-- title:
--   Countable queue chains, drift, and expected return times
-- statement:
--   Let $S$ be a countable state space and $P(i,\cdot)$ a probability mass function for each $i\in S$. This specifies a homogeneous discrete-time Markov chain. Its $n$-step probabilities are obtained by composing $P$, with the identity transition at $n=0$. The chain is irreducible when every ordered pair of states is connected by a positive-probability finite path.
--
--   For $K\subseteq S$, put $a_0(i)=1$ and
--   $$a_{n+1}(i)=\sum_{j\notin K}P(i,j)a_n(j),\qquad m_K(i)=\sum_{n\ge0}a_n(i).$$
--   Then $m_K(i)$ is the extended expected first visit to $K$ at a strictly positive time, starting from $i$. Positive recurrence means $m_{\{i\}}(i)<\infty$ for every state $i$.
--
--   For a real function $L$, the drift is $\sum_jP(i,j)(L(j)-L(i))$; a separate predicate asserts absolute summability. These notions connect a drift criterion to the actual chain rather than defining stability in terms of drift.
--
--   **Formalization Note** The definitions are polymorphic; countability and nonemptiness are imposed by the recurrence theorem. Return expectations take values in $[0,\infty]$, and non-return has infinite cost.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed pp. 210–211 (PDF pp. 218–219), Proposition D.1 and its return-time definition; DOI 10.1017/cbo9781139565363

import Mathlib

open scoped ENNReal
open Classical

open scoped NNReal

namespace KellyStochasticNetworks.MaxWeight

/-- A discrete-time transition law on a countable state space. -/
def Chain (S : Type*) := S → PMF S

/-- Probability of reaching `j` in exactly `n` transitions from `i`. -/
noncomputable def transitionPower {S : Type*} (P : Chain S) : ℕ → S → S → ℝ≥0∞
  | 0, i, j => if i = j then 1 else 0
  | n + 1, i, j => ∑' k, P i k * transitionPower P n k j

/-- Every state communicates with every other state. -/
def Irreducible {S : Type*} (P : Chain S) : Prop :=
  ∀ i j, ∃ n : ℕ, 0 < transitionPower P n i j

/-- Probability that times 1 through n all avoid K, starting from i at time 0. -/
noncomputable def avoidProbability {S : Type*} (P : Chain S) (K : Set S) :
    ℕ → S → ℝ≥0∞
  | 0, _ => 1
  | n + 1, i => ∑' j, if j ∈ K then 0 else P i j * avoidProbability P K n j

/-- Extended expected strictly positive hitting time, using the tail-sum formula.
Non-return has infinite cost, even if it occurs with positive probability less than one. -/
noncomputable def meanReturn {S : Type*} (P : Chain S) (K : Set S) (i : S) : ℝ≥0∞ :=
  ∑' n : ℕ, avoidProbability P K n i

/-- Every state has finite expected strictly positive return time. -/
def PositiveRecurrent {S : Type*} (P : Chain S) : Prop :=
  ∀ i, meanReturn P {i} i < ∞

/-- Real one-step drift; use only with the separately asserted absolute summability. -/
noncomputable def drift {S : Type*} (P : Chain S) (L : S → ℝ) (i : S) : ℝ :=
  ∑' j, (P i j).toReal * (L j - L i)

/-- Absolute integrability of a one-step increment on the countable state space. -/
def DriftIntegrable {S : Type*} (P : Chain S) (L : S → ℝ) (i : S) : Prop :=
  Summable (fun j => (P i j).toReal * |L j - L i|)

end KellyStochasticNetworks.MaxWeight


