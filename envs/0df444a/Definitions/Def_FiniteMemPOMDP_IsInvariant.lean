-- Prove2me | Definitions.Def_FiniteMemPOMDP_IsInvariant
-- name    : FiniteMemPOMDP_IsInvariant
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:30:52.932418+00:00
-- url     : https://prove2.me/theorems/a8964433-a488-4955-9828-b7521a917805
-- title:
--   $\sigma$-invariant measure on beliefs
-- statement:
--   Let $\mu\in\Delta(\Delta(\mathcal K))$ and let $\sigma:\Delta(\mathcal K)\to\Delta(\mathcal A)$ be a measurable (mixed, stationary) strategy. The measure $\mu$ is **$\sigma$-invariant** if for every continuous $f:\Delta(\mathcal K)\to[0,1]$
--
--   $$\int_{\Delta(\mathcal K)}\mathbb E\big[f(\tilde q[p,\sigma(p)])\big]\,\mu(dp)=\int_{\Delta(\mathcal K)}f(p)\,\mu(dp),$$
--
--   where the expectation is over the action $a\sim\sigma(p)$ and the next belief $\sim\tilde q[p,a]$. If the initial belief is distributed according to $\mu$ and the decision-maker plays $\sigma$, the belief at stage $2$ is again distributed according to $\mu$.
--
--   **Formalization Note** The measurability of $\sigma$ is a separate hypothesis where the predicate is used.
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, Definition A.3, p.23

import Mathlib
import Definitions.Def_FiniteMemPOMDP_beliefTransition

open MeasureTheory

namespace FiniteMemPOMDP

variable {K A S : Type} [Fintype K] [Fintype A] [Fintype S]

/-- **Invariant measure.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, Definition A.3, p.23: "Given a POMDP
Γ = (K, A, S, q, g), µ ∈ ∆(∆(K)) and σ: ∆(K) → ∆(A) measurable, we say that µ is σ-invariant if
∀f ∈ C(∆(K), [0, 1]) we have that
∫_{∆(K)} E [f(q̃[p, σ(p)])] µ(dp) = ∫_{∆(K)} f(p) µ(dp)."

`IsInvariant Γ σs μ` says: for every continuous `f : ∆(K) → [0, 1]`,
`∫ (∑_a σs(p)(a) ∫ f d q̃[p, a]) μ(dp) = ∫ f dμ`. The inner expression is
`E[f(q̃[p, σs(p)])]`, the expectation over the mixed action `a ∼ σs(p)` and the next belief
`∼ q̃[p, a]`.

**Formalization Note** `σs : ∆(K) → ∆(A)` is a (mixed) stationary strategy on beliefs; its
measurability, required by the paper, is a separate hypothesis wherever this predicate is used.
`∆(A)` is `stdSimplex ℝ A`, `∆(∆(K))` a probability measure on `stdSimplex ℝ K`. -/
def IsInvariant (Γ : POMDP K A S) (σs : stdSimplex ℝ K → stdSimplex ℝ A)
    (μ : Measure (stdSimplex ℝ K)) : Prop :=
  ∀ f : stdSimplex ℝ K → ℝ, Continuous f → (∀ p, f p ∈ Set.Icc (0 : ℝ) 1) →
    ∫ p, (∑ a, (σs p).1 a * ∫ p', f p' ∂(beliefTransition Γ p a)) ∂μ = ∫ p, f p ∂μ

end FiniteMemPOMDP


