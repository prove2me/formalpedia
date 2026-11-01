-- Prove2me | Definitions.Def_RelaxRoundPoA_Mechanism
-- name    : RelaxRoundPoA_Mechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:13.792161+00:00
-- url     : https://prove2.me/theorems/95f966e2-f815-44b9-a045-a06250d001e7
-- title:
--   Direct mechanism with a randomized outcome rule
-- statement:
--   Let $N$ be a finite set of agents and $\Omega'$ a measurable space of outcomes. A **direct mechanism** $M=(f,p)$ asks every agent $i$ to report a bid $b_i:\Omega'\to\mathbb R_{\ge0}$, a weight function on the outcomes; on the bid profile $b=(b_i)_{i\in N}$ it computes an outcome $f(b)$ and payments $p(b)$. Both may be randomized. Agents are risk neutral, so only the law of $f(b)$ and the expected payments $\mathbf E[p_i(b)]$ matter.
--
--   Here a mechanism consists of
--
--   1. for every bid profile $b$, a probability measure on $\Omega'$, the law of the outcome $f(b)$;
--   2. for every bid profile $b$ and agent $i$, a real number, agent $i$'s expected payment $\mathbf E[p_i(b)]$.
--
--   This is the object on which smoothness, the pay-your-bid rule and exact welfare maximization are defined.
--
--   **Formalization Note** The mechanism is defined on every function profile; all properties of the mission constrain it only on profiles drawn from the agents' weight classes. Expected payments are real numbers, which is more general than the paper's $p(b)\in\mathbb R_{\ge0}$: a pay-your-bid mechanism has nonnegative expected payments on profiles, and the one theorem of the mission that uses payments without assuming pay-your-bid, the implication from half-value smoothness to smoothness, does not depend on their sign.
-- source:
--   Dütting, Kesselheim, Tardos, Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round, arXiv:1511.09208v1, §2, pp.6–7

import Mathlib

open MeasureTheory NNReal

namespace RelaxRoundPoA

/-- **Direct mechanism with a randomized outcome rule.**
Dütting, Kesselheim, Tardos, *Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round*,
arXiv:1511.09208v1, §2 "Mechanism Design Basics", pp.6–7: a direct mechanism `M = (f, p)` asks the
agents `N` to report valuations (bids) `b`, computes an outcome `f(b)` with its outcome rule and
payments `p(b)` with its payment rule; "both the computation of the outcome and the payments can be
randomized". Agents are risk neutral (p.7), so only expected payments `E[p_i(b)]` enter utilities.

A mechanism is given by `outcome b`, the law of the (random) outcome `f(b)`, a probability measure on
the outcome space `Ω'`, and `expPay b i`, agent `i`'s expected payment `E[p_i(b)]`.

**Formalization Note** A bid of agent `i` is a weight function `Ω' → ℝ≥0` and a bid profile is a
plain function `b : N → Ω' → ℝ≥0`. The mechanism is total on all such functions; every property of
this mission constrains it only on profiles drawn from the agents' weight classes (`IsProfile`).
Expected payments are real numbers, which is more general than the paper's `p(b) ∈ ℝ≥0`: a
pay-your-bid mechanism has nonnegative expected payments on profiles, and the one theorem of this
mission that uses payments without assuming pay-your-bid, `isSmooth_of_half`, does not depend on
their sign. -/
structure Mechanism (N : Type*) (Ω' : Type*) [MeasurableSpace Ω'] where
  /-- The law of the outcome `f(b)` on bid profile `b`. -/
  outcome : (N → Ω' → ℝ≥0) → Measure Ω'
  /-- The outcome law is a probability measure. -/
  outcome_isProb : ∀ b, IsProbabilityMeasure (outcome b)
  /-- Agent `i`'s expected payment `E[p_i(b)]` on bid profile `b`. -/
  expPay : (N → Ω' → ℝ≥0) → N → ℝ

attribute [instance] Mechanism.outcome_isProb

end RelaxRoundPoA


