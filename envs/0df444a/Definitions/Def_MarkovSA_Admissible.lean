-- Prove2me | Definitions.Def_MarkovSA_Admissible
-- name    : MarkovSA_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:51:00.201136+00:00
-- url     : https://prove2.me/theorems/2f77a2dd-2873-443e-bf96-69829bf12741
-- title:
--   Admissible parameters $(\alpha,h)$ for $\alpha_k=\alpha/(k+h)^\xi$
-- statement:
--   For $\alpha_k=\alpha/(k+h)^\xi$ with mixing times $t_k=t_{\alpha_k}$, the pair $(\alpha,h)$ is **admissible** if
--
--   1. Condition A.1 holds;
--   2. $t_k\ge1$ for every $k$;
--   3. $\alpha_{k-t_k}\le2\alpha_k$ for every $k\ge t_k$;
--   4. if $\xi<1$, then $h\ge[2\xi/(\varphi_2\alpha)]^{1/(1-\xi)}$.
--
--   These are the conditions that the proof of Theorem A.3 (b), (c) (pp.29–30) establishes for all $h$ above a threshold $\bar h$ and then uses; Condition 2.1 (2), (3) asserts that such thresholds exist (reading R4). Item 2 is the correction C1.
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, Condition 2.1, p.6, and proof of Theorem A.3, pp.29–30 (reading R4)

import Mathlib
import Definitions.Def_MarkovSA_ConditionA1
import Definitions.Def_MarkovSA_polyStep
import Definitions.Def_MarkovSA_stepMix

namespace MarkovSA

/-- **Admissible parameters** `(α, h)` for the stepsizes `α_k = α/(k + h)^ξ` (reading R4 of Condition 2.1 (2), (3),
Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, p.6, and the proof of Theorem A.3, pp.29–30): Condition A.1 holds; `t_k ≥ 1` for all `k`
(correction C1); `α_{k−t_k} ≤ 2α_k` for all `k ≥ t_k`; and, when `ξ < 1`, `h ≥ [2ξ/(φ₂α)]^{1/(1−ξ)}`.
These are the conditions the proof of Theorem A.3 (b), (c) establishes for `h ≥ h̄` and then uses. -/
def Admissible {𝒴 : Type*} [Fintype 𝒴] [DecidableEq 𝒴] (P : Matrix 𝒴 𝒴 ℝ) (μ : 𝒴 → ℝ) (φ₂ φ₃ A a ξ h : ℝ) : Prop :=
  ConditionA1 (stepMix P μ (polyStep a h ξ)) (polyStep a h ξ) φ₂ φ₃ A ∧
    (∀ k, 1 ≤ stepMix P μ (polyStep a h ξ) k) ∧
    (∀ k, stepMix P μ (polyStep a h ξ) k ≤ k →
      polyStep a h ξ (k - stepMix P μ (polyStep a h ξ) k) ≤ 2 * polyStep a h ξ k) ∧
    (ξ < 1 → (2 * ξ / (φ₂ * a)) ^ (1 / (1 - ξ)) ≤ h)

end MarkovSA


