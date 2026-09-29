-- Prove2me | Definitions.Def_MetricalTaskSystem_Randomized_RandomizedAlgorithm
-- name    : MetricalTaskSystem_Randomized_RandomizedAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T19:17:07.483983+00:00
-- url     : https://prove2.me/theorems/b128b9fe-b244-4fc6-8ab3-1cf20258b15f
-- title:
--   Randomized on-line algorithms, expected competitiveness and the randomized competitive ratio $\bar w(S,d)$
-- statement:
--   A **randomized on-line algorithm** $R$ chooses each state at random: the $i$th state $\sigma(i)$ is drawn from a probability distribution that depends on the initial state $s_0$, the first $i$ tasks $T^1,\dots,T^i$ and the states $\sigma(0),\dots,\sigma(i-1)$ already visited. For a fixed task sequence $\mathbf T=T^1\cdots T^m$ (chosen by an *oblivious* adversary, before any random choice is made), the probability that $R$ follows the schedule $\sigma$ is
--   $$\mathrm{pr}(\sigma\mid\mathbf T)=[\sigma(0)=s_0]\prod_{i=1}^m R\big(s_0;T^1,\dots,T^i;\sigma(0),\dots,\sigma(i-1)\big)(\sigma(i)),$$
--   and the expected cost of $R$ on $\mathbf T$ is
--   $$\bar c_R(\mathbf T)=\sum_\sigma c(\mathbf T;\sigma)\,\mathrm{pr}(\sigma\mid\mathbf T).$$
--
--   For $w>0$, $R$ is **expected $w$-competitive** if there is a constant $K$ such that
--   $$\bar c_R(\mathbf T)\le w\,c_0(\mathbf T)+K$$
--   for every finite task sequence $\mathbf T$ and every initial state. The expected competitive ratio $\bar w(R)$ is the infimum of such $w$, and the **randomized competitive ratio** of the task system is
--   $$\bar w(S,d)=\inf_R \bar w(R),$$
--   the infimum over all randomized on-line algorithms, with $\inf\emptyset=+\infty$.
--
--   These are the quantities bounded by Theorem 7.1.
--
--   **Formalization Note** The paper first defines a randomized algorithm as a probability distribution on deterministic algorithms, and then describes the same notion as a scheduler–taskmaster game in which $\sigma(i)$ depends on $T^1,\dots,T^i$, $\sigma(0),\dots,\sigma(i-1)$ and random bits (p. 758). The formalization uses this second, behavioural description: a kernel `S → List (S → ℝ) → List S → PMF S`. On every finite task sequence a mixture of deterministic algorithms induces such a kernel and conversely (Kuhn's theorem for games of perfect recall), so the expected costs agree. The expected cost is a finite sum over schedules. The randomized competitive ratio is the real infimum of the set of all $w$ for which some randomized algorithm is expected $w$-competitive; this equals $\inf_R\bar w(R)$ whenever that set is nonempty (if it were empty the real `sInf` would be $0$, which is why statements about it must be read together with an existence statement).
-- source:
--   Borodin, Linial, Saks, An Optimal On-Line Algorithm for Metrical Task System, J. ACM 39(4) (1992), p. 758, Section 7

import Mathlib
import Definitions.Def_MetricalTaskSystem_Randomized_Model

namespace MetricalTaskSystem.Randomized

/-- A **randomized on-line scheduling algorithm** (p. 758), in the paper's game description:
"the `i`th state `σ(i)` is a function of the first `i` tasks `T¹, …, Tⁱ`, the first `i` states
`σ(0), σ(1), …, σ(i − 1)`, and some random bits". It is encoded as a kernel
`R s₀ [T¹, …, Tⁱ] [σ(0), …, σ(i−1)]`, the probability distribution of `σ(i)`. -/
abbrev RandomizedOnlineAlgorithm (S : Type) : Type := S → List (S → ℝ) → List S → PMF S

/-- `pr(σ | T)` (p. 758): the probability that the randomized algorithm `R`, started in `s₀`,
follows the schedule `σ : Fin (m+1) → S` on the task sequence `T : Fin m → S → ℝ`. It is `0`
unless `σ 0 = s₀`, and otherwise the product over `i = 1, …, m` of the probability that `R`
chooses `σ(i)` given `T¹, …, Tⁱ` and `σ(0), …, σ(i−1)`. The task sequence is fixed in advance
(oblivious adversary). -/
noncomputable def schedProb {S : Type} [DecidableEq S] (R : RandomizedOnlineAlgorithm S)
    (s₀ : S) {m : ℕ} (T : Fin m → S → ℝ) (σ : Fin (m + 1) → S) : ℝ :=
  if σ 0 = s₀ then
    ∏ i : Fin m,
      (R s₀ ((List.ofFn T).take (i.val + 1)) ((List.ofFn σ).take (i.val + 1)) (σ i.succ)).toReal
  else 0

/-- The expected cost `c̄_R(T) = Σ_σ c(T; σ) · pr(σ | T)` of a randomized on-line algorithm
(p. 758), a finite sum over all schedules. -/
noncomputable def expCost {S : Type} [Fintype S] [DecidableEq S] (d : S → S → ℝ)
    (R : RandomizedOnlineAlgorithm S) (s₀ : S) {m : ℕ} (T : Fin m → S → ℝ) : ℝ :=
  ∑ σ : Fin (m + 1) → S, schedProb R s₀ T σ * schedCost d T σ

/-- `R` is **expected `w`-competitive** (p. 758): `w > 0` and `c̄_R(T) − w·c₀(T)` is bounded
above by a constant `K` over all finite task sequences `T` (and initial states `s₀`). Tasks are
finite and nonnegative. The inequality is written additively. -/
def IsExpCompetitive {S : Type} [Fintype S] [DecidableEq S] (d : S → S → ℝ)
    (R : RandomizedOnlineAlgorithm S) (w : ℝ) : Prop :=
  0 < w ∧ ∃ K : ℝ, ∀ (s₀ : S) (m : ℕ) (T : Fin m → S → ℝ), (∀ i s, 0 ≤ T i s) →
    expCost d R s₀ T ≤ w * offlineOpt d s₀ T + K

/-- The **randomized competitive ratio** `w̄(S, d)` of the task system (p. 758): the infimum over
randomized on-line algorithms `R` of `w̄(R) = inf {w : R is expected w-competitive}`. It is
written as the infimum of the union of these sets, which has the same value as
`inf_R w̄(R)` with the convention `inf ∅ = +∞`. (If the union were empty, the real `sInf`
would be `0`.) -/
noncomputable def randomizedRatio {S : Type} [Fintype S] [DecidableEq S]
    (d : S → S → ℝ) : ℝ :=
  sInf {w : ℝ | ∃ R : RandomizedOnlineAlgorithm S, IsExpCompetitive d R w}

end MetricalTaskSystem.Randomized


