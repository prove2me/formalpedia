-- Prove2me | Definitions.Def_GradedReserve_IsSymBNE
-- name    : GradedReserve_IsSymBNE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:33:27.903215+00:00
-- url     : https://prove2.me/theorems/c80ecf0e-4d0e-4ace-8a07-bec51ff56183
-- title:
--   Symmetric Bayes–Nash equilibrium of $G_\pi$ (mixed strategies allowed)
-- statement:
--   A **symmetric Bayes–Nash equilibrium** of $G_\pi$ is a mixed strategy $\sigma$, used by every bidder, such that
--
--   1. for every value $v\in[0,1]$, $\sigma(v)$ is a probability distribution over actions that puts no mass on bids above $1$;
--   2. for almost every type $v$, $\sigma(v)$ is a best response: no action yields a higher payoff than the expected payoff of $\sigma(v)$,
--   $$u(v,a)\le\int u(v,a')\,\sigma(v)(da')\qquad\text{for every action }a.$$
--
--   Bidders are risk neutral, their randomizations are independent, and the exit action is always available.
--
--   **Formalization Note** Best responses are required for almost every type (with respect to the value law), as in the paper's proofs. Mixed strategies are measurable in the value (Markov kernels).
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 2 and Definition 2.1, p.4 (PDF 5); proof of Lemma 3.3, p.13 (PDF 14)

import Mathlib
import Definitions.Def_GradedReserve_typeMeasure
import Definitions.Def_GradedReserve_payoff
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- A symmetric Bayes–Nash equilibrium of `G_π`, mixed strategies allowed (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section 2 and
Definition 2.1, p.4, PDF 5; "allowing mixed strategies", proof of Lemma 3.3, p.13, PDF 14): every
bidder uses the Markov kernel `σ`; for every value in `[0, 1]`, `σ v` is a probability measure on
actions with no mass above `1` (bids lie in `[0, 1]`, exits are negative actions); and almost
every type (with respect to the value law) best-responds: no action gives it a higher payoff than
the expected payoff of `σ v`.

**Formalization Note.** Best responses are required for almost every type, as in the paper's
proofs ("apart from a null set", p.14). Mixed strategies are Markov kernels (measurable in the
value). -/
def IsSymBNE (f : ℝ → ℝ) (n : ℕ) (π : ℝ → ℝ) (σ : Kernel ℝ ℝ) : Prop :=
  (∀ v ∈ Icc (0:ℝ) 1, IsProbabilityMeasure (σ v) ∧ σ v (Ioi 1) = 0) ∧
  ∀ᵐ v ∂(typeMeasure f), ∀ a : ℝ, payoff f n π σ v a ≤ ∫ a', payoff f n π σ v a' ∂(σ v)

end GradedReserve


