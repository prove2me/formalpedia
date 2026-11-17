-- Prove2me | Definitions.Def_SemiBanditSOO_Supplement_Learner
-- name    : SemiBanditSOO_Supplement_Learner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:16:32.348411+00:00
-- url     : https://prove2.me/theorems/1fadeb79-44c3-46b2-a472-b68545e9c677
-- title:
--   Randomized learning algorithms and their cumulative expected regret $R_T(D)$
-- statement:
--   The learner faces the same problem in each of $T$ rounds. It knows the problem and $T$, but not the product distribution $D=\prod_i D_i$. In each round $t$, a vector $X^t\sim D$ is drawn independently of the previous rounds, and the learner chooses a deterministic policy $\sigma^t$ based on the observations of the previous rounds and on internal randomness. A **randomized learning algorithm** on a probability space $(\Xi,\mu)$ of internal randomness is a rule
--   $$(t,\xi,X^1,\dots,X^T)\mapsto\sigma^t_{\xi}(X^1,\dots,X^{t-1})$$
--   such that:
--
--   1. every $\sigma^t_\xi(\cdot)$ is a policy: at each non-leaf node it chooses a feasible action, depending only on the observed coordinates, measurably;
--   2. $\sigma^t$ depends on the round vectors only through the rounds before $t$;
--   3. the choice is jointly measurable in the internal randomness, the history and the current observations.
--
--   Its **cumulative expected regret** is
--   $$R_T(D)=\sum_{t=1}^T\Bigl(\mathrm{OPT}(D)-\mathbb E\bigl[f(\sigma^t,X^t)\bigr]\Bigr),$$
--   where the expectation is over $\xi\sim\mu$ and the i.i.d. round vectors $X^1,\dots,X^T\sim D$, independent of $\xi$, and $\mathrm{OPT}(D)$ is the benchmark of the base mission.
--
--   This is the class of algorithms over which the lower bound of Theorem 3.6 is stated.
--
--   **Formalization Note.** The learner may use the full past round vectors, not only their observed coordinates; every semi-bandit learner is such a learner, so a lower bound over this class implies one over semi-bandit learners, and under full feedback the two classes coincide. Internal randomness drawn once on an arbitrary probability space covers fresh randomness in every round and randomized policies within a round. Rounds are numbered $0,\dots,T-1$.
-- source:
--   Harada, Kawase, Sumita, Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback, arXiv:2611.02739v1, §2.1, p.7 (learner, R_T); Theorem 3.6, p.12; §6.2, p.31

import Mathlib
import Definitions.Def_SemiBanditSOO_Model
import Definitions.Def_SemiBanditSOO_Algorithm

open MeasureTheory

namespace SemiBanditSOO.Supplement

/-- **Randomized learning algorithms** (§2.1, p.7; used in Theorem 3.6, p.12, and §6.2, p.31).
Harada, Kawase, Sumita, *Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit
Feedback*, arXiv:2611.02739v1, §2.1, p.7.

The learner faces the same problem `Pb` in each of `T` rounds; it knows the problem and `T`, but not
the distributions. In round `t` it chooses a deterministic policy based on the observations of the
previous rounds and on internal randomness `ξ ∈ Ξ`, drawn once before the first round from a
probability measure on `Ξ`. A learner on `Ξ` consists of

1. `pol t ξ ω`, the policy of round `t` (0-based) for internal randomness `ξ` and round vectors
   `ω = (X^0, …, X^{T-1})`, which is a (feasible, observation-dependent, measurable) policy
   (`isPolicy`);
2. causality: `pol t ξ ω` depends on `ω` only through the rounds `τ < t` (`causal`);
3. joint measurability of the choice in `(ξ, ω, x)` (`measurable`), so that the expected reward of
   round `t` is a genuine integral.

**Formalization Note.**
* The learner may use the full past vectors `X^τ`, `τ < t`, not only the observed coordinates
  `X^τ_{obs(ℓ^τ)}`. Every semi-bandit learner is such a learner, so a lower bound over this class
  is at least as strong as one over semi-bandit learners; under full feedback the classes coincide.
* Internal randomness drawn once on an arbitrary probability space covers fresh randomness in
  every round (take a product space) and randomized policies within a round (a distribution over
  deterministic policies). -/
structure Learner {n : ℕ} {dom : Fin n → Set ℝ} {V : Type} (Pb : Problem n dom V) (T : ℕ)
    (Ξ : Type) [MeasurableSpace Ξ] where
  /-- The policy of round `t` given internal randomness `ξ` and the round vectors `ω`. -/
  pol : Fin T → Ξ → (Fin T → Obs dom) → V → Obs dom → V
  /-- Every chosen rule is a policy (§2.1, p.7). -/
  isPolicy : ∀ t ξ ω, Pb.IsPolicy (pol t ξ ω)
  /-- The round-`t` policy depends only on the rounds before `t`. -/
  causal : ∀ (t : Fin T) (ξ : Ξ) (ω ω' : Fin T → Obs dom),
    (∀ τ : Fin T, τ < t → ω τ = ω' τ) → pol t ξ ω = pol t ξ ω'
  /-- Joint measurability in the internal randomness, the history and the current observations. -/
  measurable : ∀ (t : Fin T) (u v : V),
    MeasurableSet {p : Ξ × (Fin T → Obs dom) × Obs dom | pol t p.1 p.2.1 u p.2.2 = v}

/-- **The cumulative expected regret of a randomized learner** (§2.1, p.7):
`R_T(D) = Σ_{t=1}^T (OPT(D) − 𝔼[f(σ^t, X^t)])`, where `σ^t` is the learner's policy in round `t`
and the expectation is over the internal randomness `ξ ∼ μ` and the i.i.d. round vectors
`X^1, …, X^T ∼ D`, independent of `ξ`.

**Formalization Note.** Rounds are numbered `0, …, T − 1`; `OPT(D)` is the published
`Problem.OPT` (a supremum over measurable deterministic policies). -/
noncomputable def Learner.regret {n : ℕ} {dom : Fin n → Set ℝ} {V : Type} {Pb : Problem n dom V}
    {T : ℕ} {Ξ : Type} [MeasurableSpace Ξ] (L : Learner Pb T Ξ) (μ : Measure Ξ)
    (D : ∀ i, ProbabilityMeasure (dom i)) : ℝ :=
  ∑ t : Fin T, (Pb.OPT D -
    ∫ p : Ξ × (Fin T → Obs dom), Pb.payoff (L.pol t p.1 p.2) (p.2 t) ∂(μ.prod (roundsMeasure D T)))

end SemiBanditSOO.Supplement


