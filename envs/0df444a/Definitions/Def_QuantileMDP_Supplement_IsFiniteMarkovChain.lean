-- Prove2me | Definitions.Def_QuantileMDP_Supplement_IsFiniteMarkovChain
-- name    : QuantileMDP_Supplement_IsFiniteMarkovChain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:53:19.737691+00:00
-- url     : https://prove2.me/theorems/39f8e122-5303-56b1-b2f6-08c93fa28ec1
-- title:
--   Real-valued Markov chain $X_0,\dots,X_{T-1}$ with a finite state space
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $T\in\mathbb N$. A family $X_0,\dots,X_{T-1}:\Omega\to\mathbb R$ is a **real-valued Markov chain with a finite state space** when
--
--   1. each $X_t$ is a random variable (measurable);
--   2. there is a finite set $F\subset\mathbb R$ with $X_t(\omega)\in F$ for all $t<T$ and all $\omega$;
--   3. for every $t$ with $t+1<T$, all $x_0,\dots,x_t\in\mathbb R$ with $P(X_0=x_0,\dots,X_t=x_t)>0$, and every $y\in\mathbb R$,
--   $$
--   P(X_{t+1}=y\mid X_0=x_0,\dots,X_t=x_t)=P(X_{t+1}=y\mid X_t=x_t).
--   $$
--
--   The chain need not be time-homogeneous. This is the hypothesis of Theorem 5 of Li, Zhong and Brandeau on the two processes whose cumulative rewards are compared.
--
--   **Formalization Note** The chain is a sequence `X : ℕ → Ω → ℝ`; only the indices $t<T$ are constrained. Conditional probabilities are `ProbabilityTheory.cond`.
-- source:
--   Li, Zhong, Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §5.2, Theorem 5, p.22

import Mathlib

open MeasureTheory ProbabilityTheory

namespace QuantileMDP.Supplement

/-- `X_0, …, X_{T-1}` is a real-valued Markov chain with a finite state space on the probability
space `(Ω, P)`: each `X_t` (`t < T`) is measurable, all of them take values in one finite set of
reals, and for `t + 1 < T` the next state depends on the past only through the present,
`P(X_{t+1} = y | X_0 = x_0, …, X_t = x_t) = P(X_{t+1} = y | X_t = x_t)` whenever the history event
has positive probability.
Li, Zhong, Brandeau, *Quantile Markov Decision Processes*, arXiv:1711.05788v5, §5.2, Theorem 5,
p.22 ("two real-value Markov chains with a finite state space, `{X_t}_{t=0}^{T-1}`").

**Formalization Note** The chain is a family `X : ℕ → Ω → ℝ`; only the indices `t < T` are
constrained, the values at `t ≥ T` are irrelevant. Conditional probabilities are
`ProbabilityTheory.cond`. The chain is not assumed time-homogeneous. -/
def IsFiniteMarkovChain {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (T : ℕ)
    (X : ℕ → Ω → ℝ) : Prop :=
  (∀ t < T, Measurable (X t)) ∧
  (∃ F : Finset ℝ, ∀ t < T, ∀ ω, X t ω ∈ F) ∧
  (∀ t, t + 1 < T → ∀ (x : Fin (t + 1) → ℝ) (y : ℝ),
    P {ω | ∀ j : Fin (t + 1), X j ω = x j} ≠ 0 →
      cond P {ω | ∀ j : Fin (t + 1), X j ω = x j} {ω | X (t + 1) ω = y} =
        cond P {ω | X t ω = x (Fin.last t)} {ω | X (t + 1) ω = y})

end QuantileMDP.Supplement


