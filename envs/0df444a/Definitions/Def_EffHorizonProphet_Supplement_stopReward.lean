-- Prove2me | Definitions.Def_EffHorizonProphet_Supplement_stopReward
-- name    : EffHorizonProphet_Supplement_stopReward
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:55:31.120452+00:00
-- url     : https://prove2.me/theorems/01899b64-22e4-4043-be4d-d390468cf6de
-- title:
--   Expected reward $\mathbb E_D[X_\tau]$ of a stopping rule
-- statement:
--   For a common decay factor $\tilde\gamma$, a phase-length profile $(n_1,\dots,n_S)$ with $n=\sum_s n_s$, a base law $D$ and a stopping rule $\tau$, the **expected reward** is
--   $$\mathbb E_D[X_\tau],\qquad X_i=\tilde\gamma^{s-1}Y_i\ \ (i\in T_s),$$
--   with payoff $0$ if $\tau$ never stops, the expectation being over $n$ i.i.d. pairs $(Y_i,U_i)$, $Y_i\sim D$, $U_i\sim\mathrm{Unif}[0,1]$.
--
--   **Formalization Note** This is a Bochner integral under the published product law `sampleLaw`; for a stopping rule and an admissible law the integrand is measurable and integrable.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Section 3, p.3

import Mathlib
import Definitions.Def_EffHorizonProphet_reward
import Definitions.Def_EffHorizonProphet_sampleLaw

open MeasureTheory

namespace EffHorizonProphet.Supplement

/-- The **expected reward `E_D[X_τ]` of a stopping rule** `τ` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Section 3, p.3), with payoff
`0` when `τ` never stops.

**Formalization Note** `n = ∑ s, L s` stages, `0`-based; `τ ω = n` (or larger) pays `0`. The
expectation is taken under the product law `sampleLaw D L` of the stage pairs `(Y_i, U_i)`. For a
stopping rule and an admissible law the integrand is measurable and integrable. -/
noncomputable def stopReward {S : ℕ} (γ : ℝ) (L : Fin S → ℕ) (D : Measure ℝ)
    (τ : (Fin (∑ s, L s) → ℝ × unitInterval) → ℕ) : ℝ :=
  ∫ ω, (if h : τ ω < ∑ s, L s then reward γ L ⟨τ ω, h⟩ ω else 0) ∂sampleLaw D L

end EffHorizonProphet.Supplement


