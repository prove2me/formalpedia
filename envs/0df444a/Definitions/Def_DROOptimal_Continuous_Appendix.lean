-- Prove2me | Definitions.Def_DROOptimal_Continuous_Appendix
-- name    : DROOptimal_Continuous_Appendix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:36.963217+00:00
-- url     : https://prove2.me/theorems/e6706494-168e-4ecf-ad72-4d7323362e39
-- title:
--   (33), (34), (23), (35), pp. 24–31 — the predictor ĉ_{r,ϵ} of (34) and the dual objective α − e^{−r} exp(∫ log(α − γ) dℙ′)
-- statement:
--   This module defines the auxiliary objects of Appendix A used to analyse the distributionally robust predictor $\hat c_r$ in the continuous setting. Let $\bar\gamma(x)=\max_{\xi\in\Xi}\gamma(x,\xi)$ and $c(x,\mathbb P)=\int_\Xi\gamma(x,\xi)\,\mathrm d\mathbb P(\xi)$.
--
--   1. **The absolutely continuous problem** (34). For $r$ and $\epsilon$,
--   $$
--   \hat c_{r,\epsilon}(x,\mathbb P')=\sup_{\substack{\mathbb P_c\in\mathcal P\\ p\in[0,1]}}\Big\{p\cdot\int_\Xi\gamma(x,\xi)\,\mathrm d\mathbb P_c(\xi)+(1-p)\cdot(\bar\gamma(x)+\epsilon)\ :\ \mathbb P'\ll p\cdot\mathbb P_c\ll\mathbb P',\ \int_\Xi\log\Big(\frac1p\cdot\frac{\mathrm d\mathbb P'}{\mathrm d\mathbb P_c}(\xi)\Big)\mathrm d\mathbb P'(\xi)\le r\Big\}.
--   $$
--   At $\epsilon=0$ this is the right-hand side of (33).
--   2. **The geometric mean.** For $\alpha\ge\bar\gamma(x)$, $\exp\big(\int_\Xi\log(\alpha-\gamma(x,\xi))\,\mathrm d\mathbb P'(\xi)\big)$, with the convention $\log0=-\infty$ and $\exp(-\infty)=0$.
--   3. **The dual objective** of (23) and (35):
--   $$
--   \alpha-e^{-r}\cdot\exp\Big(\int_\Xi\log(\alpha-\gamma(x,\xi))\,\mathrm d\mathbb P'(\xi)\Big).
--   $$
--
--   These objects appear in the dual representations of $\hat c_r$ (Proposition 5) and of $\hat c_{r,\epsilon}$ (Lemma 4), which the paper uses to prove that $\hat c_r$ is continuous.
--
--   **Formalization Note** The integral constraint of (34) carries an explicit integrability requirement: when $\mathbb P'\ll\mathbb P_c$ and the integrand is not $\mathbb P'$-integrable, the paper's integral is $+\infty$ and the constraint fails, while Lean's Bochner integral would return $0$. The geometric mean is defined as $\inf_{\delta>0}\exp\big(\int_\Xi\log(\alpha+\delta-\gamma(x,\xi))\,\mathrm d\mathbb P'(\xi)\big)$ (the infimum over the subtype $\delta>0$). For $\alpha>\bar\gamma(x)$ this is $\exp\big(\int\log(\alpha-\gamma)\,\mathrm d\mathbb P'\big)$; at $\alpha=\bar\gamma(x)$ it is the monotone limit, equal to the paper's value under $\log0=-\infty$. Its value for $\alpha<\bar\gamma(x)$ is never used.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 29 (33), p. 31 (34), (35), p. 24 (23), p. 32 (convention log 0 = −∞)

import Mathlib
import Definitions.Def_DROOptimal_Continuous_Setting

namespace DROOptimal.Continuous

open MeasureTheory
open scoped ENNReal

variable {d n : ℕ} {Ξ : Set (EuclideanSpace ℝ (Fin d))} {X : Set (EuclideanSpace ℝ (Fin n))}

/-- The feasible set of problems (33) and (34) (pp. 29, 31): pairs `(ℙ_c, p) ∈ 𝒫 × [0, 1]` with
`ℙ′ ≪ p · ℙ_c ≪ ℙ′` and `∫_Ξ log((1/p) · dℙ′/dℙ_c(ξ)) dℙ′(ξ) ≤ r`. The integral constraint is read
with an explicit integrability conjunct: when `ℙ′ ≪ ℙ_c` and the integrand is not `ℙ′`-integrable,
the paper's integral is `+∞` and the constraint fails. -/
def acFeasible (r : ℝ) (ℙ' : Dist Ξ) : Set (Dist Ξ × ℝ) :=
  {q | q.2 ∈ Set.Icc (0 : ℝ) 1 ∧
    (ℙ' : Measure ↥Ξ) ≪ ENNReal.ofReal q.2 • (q.1 : Measure ↥Ξ) ∧
    ENNReal.ofReal q.2 • (q.1 : Measure ↥Ξ) ≪ (ℙ' : Measure ↥Ξ) ∧
    Integrable (fun ξ => Real.log (1 / q.2 * ((ℙ' : Measure ↥Ξ).rnDeriv q.1 ξ).toReal))
      (ℙ' : Measure ↥Ξ) ∧
    ∫ ξ, Real.log (1 / q.2 * ((ℙ' : Measure ↥Ξ).rnDeriv q.1 ξ).toReal) ∂(ℙ' : Measure ↥Ξ) ≤ r}

/-- The predictor `ĉ_{r,ϵ}` of (34) (p. 31):
`sup { p · ∫_Ξ γ(x, ξ) dℙ_c(ξ) + (1 − p) · (γ̄(x) + ϵ) : (ℙ_c, p) feasible }`.
At `ϵ = 0` this is the right-hand side of (33) (Lemma 2, p. 29). -/
noncomputable def acPredictor (γ : ↥X → ↥Ξ → ℝ) (r ε : ℝ) (x : ↥X) (ℙ' : Dist Ξ) : ℝ :=
  sSup ((fun q : Dist Ξ × ℝ => q.2 * cost γ x q.1 + (1 - q.2) * (worstCost γ x + ε)) ''
    acFeasible r ℙ')

/-- The geometric mean `exp(∫_Ξ log(α − γ(x, ξ)) dℙ′(ξ))` of (23) and (35), for `α ≥ γ̄(x)`, with the
paper's convention `log 0 = −∞` (p. 32). It is defined as the infimum over `δ > 0` of
`exp(∫_Ξ log(α + δ − γ(x, ξ)) dℙ′(ξ))`; for `α > γ̄(x)` this equals `exp(∫_Ξ log(α − γ(x, ξ)) dℙ′(ξ))`,
and at `α = γ̄(x)` it is the monotone limit, i.e. the paper's value (`0` when the integral is `−∞`).
Values at `α < γ̄(x)` are never used. -/
noncomputable def geoMean (γ : ↥X → ↥Ξ → ℝ) (x : ↥X) (ℙ' : Dist Ξ) (α : ℝ) : ℝ :=
  ⨅ δ : Set.Ioi (0 : ℝ), Real.exp (∫ ξ, Real.log (α + (δ : ℝ) - γ x ξ) ∂(ℙ' : Measure ↥Ξ))

/-- The objective `α − e^{−r} · exp(∫_Ξ log(α − γ(x, ξ)) dℙ′(ξ))` of the univariate problems (23) and
(35) (pp. 24, 31). -/
noncomputable def dualObjective (γ : ↥X → ↥Ξ → ℝ) (r : ℝ) (x : ↥X) (ℙ' : Dist Ξ) (α : ℝ) : ℝ :=
  α - Real.exp (-r) * geoMean γ x ℙ' α

end DROOptimal.Continuous


