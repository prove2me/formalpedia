-- Prove2me | Definitions.Def_FairReplay_expectedRounds
-- name    : FairReplay_expectedRounds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:46:28.95883+00:00
-- url     : https://prove2.me/theorems/20c07687-fcad-4d3d-9506-0907c854dc67
-- title:
--   Expected number of rounds $\mathbb E_\nu[T]$
-- statement:
--   For an environment $\nu$, a policy $\pi$ and a stopping time $\tau$, the **expected number of rounds** is
--
--   $$
--   \mathbb E_{\nu}[\tau]=\int\tau\,d\mathbb P_{\nu\pi}\in[0,\infty],
--   $$
--
--   the expectation of $\tau$ under the law of the interaction trajectory. It is $\infty$ whenever $\tau=\infty$ with positive probability. On the null environment this is the paper's $\mathbb E_0[T]$.
--
--   **Formalization Note** A lower Lebesgue integral in $[0,\infty]$; "finite expected stopping time" is $\mathbb E_\nu[\tau]<\infty$.
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.4, eqs. (34), (36), p.14 (PDF p.16)

import Mathlib
import Definitions.Def_BanditTrajectory

open MeasureTheory

namespace FairReplay

/-- **Expected number of rounds** `E_ν[T]` (Sah, Zhang, Lian, *Testing Fairness of Evolving
Software under Uncertainty*, STOC 2027 submission, manuscript of 2026-11-03, sha256 e23940a0…,
Theorem 10.4, p.14 (PDF p.16): "E0[T]").

`expectedRounds ν π τ` is the expectation of the stopping time `τ` under the trajectory law of the
policy `π` in the environment `ν`, computed in `[0, ∞]`.

**Formalization Note** The expectation is a lower Lebesgue integral in `ℝ≥0∞`, so it is `∞` when
`τ = ⊤` with positive probability; "finite expected stopping time" is `expectedRounds ν π τ < ⊤`. -/
noncomputable def expectedRounds {k : ℕ} (ν : BanditAlgorithm.StochasticBandit k)
    (π : BanditAlgorithm.BanditPolicy k) (τ : (ℕ → Fin k × ℝ) → ℕ∞) : ENNReal :=
  ∫⁻ ω, (τ ω : ENNReal) ∂BanditAlgorithm.banditTrajMeasure ν π

end FairReplay


