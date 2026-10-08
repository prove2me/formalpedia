-- Prove2me | Definitions.Def_JSQHalfinWhitt_Tightness_Stationary
-- name    : JSQHalfinWhitt_Tightness_Stationary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:43:56.054579+00:00
-- url     : https://prove2.me/theorems/380329b8-a951-4848-adee-5d776ae142c2
-- title:
--   Expectations, probabilities and stationary distributions of a chain with generator $G$ (global balance $\pi G = 0$)
-- statement:
--   Let $S$ be a countable state space and let $G$ be the generator of a continuous-time Markov chain on $S$, acting on functions $f : S \to \mathbb R$. A law on $S$ is given by its probabilities $\pi(q) = P(Q = q)$.
--
--   1. The **expectation** of $h(Q)$ is the series $\mathbb E\,h(Q) = \sum_{q \in S} \pi(q)\,h(q)$.
--   2. The **probability** of an event $A$ is $P(A(Q)) = \sum_{q \in S,\ A(q)} \pi(q)$.
--   3. For a state $q'$, $1_{q'}$ is the indicator function of $\{q'\}$.
--   4. $\pi$ is a **stationary distribution** of the chain when $\pi(q) \ge 0$ for all $q$, $\sum_q \pi(q) = 1$, and $\pi$ satisfies the global balance equations $\pi G = 0$: for every state $q'$ the series
--   $$\sum_{q \in S} \pi(q)\,(G 1_{q'})(q)$$
--   converges and equals $0$.
--
--   Since $(G 1_{q'})(q)$ is the transition rate from $q$ to $q'$ when $q \ne q'$ and minus the total exit rate of $q'$ when $q = q'$, item 4 is the familiar condition "rate of flow into $q'$ equals rate of flow out of $q'$". These are the notions in which the stationary moment bounds of the join-the-shortest-queue mission are stated.
--
--   **Formalization Note** The paper speaks of random variables "having the stationary distribution" of the chain and uses only the relation $\mathbb E\,G_Q f(Q) = 0$ (its Lemma 1). For a chain with bounded transition rates, such as the join-the-shortest-queue chain (exit rates below $n\lambda + n$, p. 21), the chain is non-explosive and uniformizable, and the probability solutions of $\pi G = 0$ are exactly its stationary distributions; this predicate is therefore used in place of a construction of the process. The expectation is a `tsum`; statements that use it either assume the summability they need or apply it to bounded functions.
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), pp. 1, 5, 6, 21: 'random variables having the stationary distributions' (p. 5), expectations and probabilities as used in Lemmas 1–2 (p. 6), exit-rate bound in the proof of Lemma 1 (p. 21)

import Mathlib

namespace JSQHalfinWhitt.Tightness

open scoped Classical

/-- The expectation `E h(Q) = ∑_q π(q) h(q)` of a function `h` of a random state `Q` whose law on
the countable state space `S` has probabilities `π q = P(Q = q)`. It is a `tsum`; every statement
that uses it either states the summability it needs or uses a bounded `h`. -/
noncomputable def expect {S : Type*} (π : S → ℝ) (h : S → ℝ) : ℝ :=
  ∑' q, π q * h q

/-- The probability `P(A(Q)) = ∑_{q : A q} π(q)` of the event `{A(Q)}` under the law `π`. -/
noncomputable def prob {S : Type*} (π : S → ℝ) (A : S → Prop) : ℝ :=
  ∑' q, if A q then π q else 0

/-- The indicator `1_{q'}` of a single state `q'`. -/
noncomputable def indicatorState {S : Type*} (q' : S) : S → ℝ :=
  fun r => if r = q' then 1 else 0

/-- `π` is a stationary distribution of the continuous-time Markov chain on the countable state
space `S` whose generator `G` acts on functions `f : S → ℝ`: `π` is a probability distribution on
`S` and it satisfies the global balance equations `π G = 0`, i.e. for every state `q'`,
`∑_q π(q) (G 1_{q'})(q) = 0` (the sum converging). For a chain with bounded transition rates, such
as the join-the-shortest-queue chain this is used for, the probability solutions of `π G = 0` are
exactly the stationary distributions of the chain. -/
def IsStationaryDist {S : Type*} (G : (S → ℝ) → S → ℝ) (π : S → ℝ) : Prop :=
  (∀ q, 0 ≤ π q) ∧ Summable π ∧ ∑' q, π q = 1 ∧
    ∀ q' : S, Summable (fun q => π q * G (indicatorState q') q) ∧
      ∑' q, π q * G (indicatorState q') q = 0

end JSQHalfinWhitt.Tightness


