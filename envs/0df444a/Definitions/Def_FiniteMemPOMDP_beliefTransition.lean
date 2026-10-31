-- Prove2me | Definitions.Def_FiniteMemPOMDP_beliefTransition
-- name    : FiniteMemPOMDP_beliefTransition
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:29:53.300327+00:00
-- url     : https://prove2.me/theorems/9ec89588-6b62-4719-b057-18bfefb03348
-- title:
--   Bayes belief transition $\tilde q:\Delta(\mathcal K)\times\mathcal A\to\Delta(\Delta(\mathcal K))$
-- statement:
--   When the belief is $p$ and the action $a$ is played, the signal $s$ has probability $P_{p,a}(s)=\sum_{k,k'}p(k)\,q(k,a)(k',s)$, and the next belief is the Bayes posterior
--
--   $$k'\mapsto\frac{\sum_k p(k)\,q(k,a)(k',s)}{P_{p,a}(s)} .$$
--
--   The **belief transition** $\tilde q[p,a]\in\Delta(\Delta(\mathcal K))$ is the law of the next belief: it puts mass $P_{p,a}(s)$ on the posterior after $s$, for each signal $s$.
--
--   **Formalization Note** $\Delta(\Delta(\mathcal K))$ is a measure on `stdSimplex ℝ K`; the posterior after a signal of probability $0$ is set to $p$ and carries no mass.
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, Definition A.3, p.23

import Mathlib
import Definitions.Def_FiniteMemPOMDP_POMDP

open MeasureTheory

namespace FiniteMemPOMDP

variable {K A S : Type} [Fintype K]

/-- The probability `∑_{k, k'} p(k) q(k, a)(k', s)` of the signal `s` when the belief is `p` and
the action is `a`. -/
noncomputable def signalProb (Γ : POMDP K A S) (p : stdSimplex ℝ K) (a : A) (s : S) : ℝ :=
  ∑ k, ∑ k', p.1 k * (Γ.q k a (k', s)).toReal

/-- The Bayes posterior on the next state after the belief `p`, the action `a` and the signal
`s`: `k' ↦ ∑_k p(k) q(k, a)(k', s) / P(s)`; equal to `p` when the signal has probability `0`
(that value is never charged by `beliefTransition`). -/
noncomputable def bayes (Γ : POMDP K A S) (p : stdSimplex ℝ K) (a : A) (s : S) : stdSimplex ℝ K :=
  if hpos : 0 < signalProb Γ p a s then
    ⟨fun k' => (∑ k, p.1 k * (Γ.q k a (k', s)).toReal) / signalProb Γ p a s,
      fun _ => div_nonneg (Finset.sum_nonneg fun k _ => mul_nonneg (p.2.1 k) ENNReal.toReal_nonneg)
        hpos.le,
      by rw [← Finset.sum_div, Finset.sum_comm]; exact div_self hpos.ne'⟩
  else p

/-- **The belief transition `q̃ : ∆(K) × A → ∆(∆(K))`.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, Definition A.3, p.23: "q̃: ∆(K) × A → ∆(∆(K))
is the natural transition in ∆(K) from one belief to another, given by Bayes rule."

`beliefTransition Γ p a` is the law of the next belief: it charges the Bayes posterior
`bayes Γ p a s` with the probability `P_{p,a}(s)` of the signal `s`, for each signal `s`.

**Formalization Note** `∆(∆(K))` is a measure on `stdSimplex ℝ K` (with its Borel σ-algebra); the
measure is the finite sum `∑_s P_{p,a}(s) δ_{bayes(p, a, s)}`, a probability measure. -/
noncomputable def beliefTransition [Fintype S] (Γ : POMDP K A S) (p : stdSimplex ℝ K) (a : A) :
    Measure (stdSimplex ℝ K) :=
  ∑ s, ENNReal.ofReal (signalProb Γ p a s) • Measure.dirac (bayes Γ p a s)

end FiniteMemPOMDP


