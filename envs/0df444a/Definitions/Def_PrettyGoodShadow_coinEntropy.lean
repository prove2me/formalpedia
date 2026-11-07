-- Prove2me | Definitions.Def_PrettyGoodShadow_coinEntropy
-- name    : PrettyGoodShadow_coinEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:22:40.074494+00:00
-- url     : https://prove2.me/theorems/c867ba9c-59c1-4db7-b993-9f20af6a8e19
-- title:
--   Mixed coin law and Shannon entropy $H(z_1,\dots,z_n)$
-- statement:
--   Let $\theta$ be a random variable on $[0,1]$ with law $\mu$, and let $z_1,\dots,z_n$ be conditionally independent $\mathrm{Ber}(\theta)$ given $\theta$. Their joint law and entropy are
--
--   $$
--   \Pr[z]=\mathbb E_\theta\prod_i\theta^{z_i}(1-\theta)^{1-z_i},\qquad H(z_1,\dots,z_n)=-\sum_z\Pr[z]\log\Pr[z].
--   $$
--
--   **Formalization Note** Entropy in nats, with $0\log0=0$. For $\mu$ carried by $[0,1]$ the integrand is bounded and measurable, so the integral is not a junk value.
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), Lemma 4.13, p.27

import Mathlib

namespace PrettyGoodShadow

open MeasureTheory

/-- **Probability of a coin string** `z` under independent tosses of a coin of bias `θ`: `∏_i Ber(θ)(z_i)`,
with `true` for outcome `1` (arXiv:2610.06781, sha256 bd055b7d…, Lemma 4.13, p.27). -/
def coinWeight {n : ℕ} (θ : ℝ) (z : Fin n → Bool) : ℝ :=
  ∏ i, if z i then θ else 1 - θ

/-- **Marginal law of `z_1, …, z_n`**, conditionally i.i.d. `Ber(θ)` given `θ ∼ μ` (arXiv:2610.06781, sha256
bd055b7d…, Lemma 4.13, p.27): `Pr[z] = E_θ ∏_i Ber(θ)(z_i)`.

**Formalization Note** `μ` is a probability measure on `ℝ` carried by `[0, 1]`. The integrand is then a
bounded measurable function, so the Bochner integral is not a junk value. -/
noncomputable def coinLaw (μ : Measure ℝ) {n : ℕ} (z : Fin n → Bool) : ℝ :=
  ∫ θ, coinWeight θ z ∂μ

/-- **Shannon entropy** `H(z_1, …, z_n)` in nats (arXiv:2610.06781, sha256 bd055b7d…, Lemma 4.13, p.27), with
`−0 log 0 = 0`. -/
noncomputable def coinEntropy (μ : Measure ℝ) (n : ℕ) : ℝ :=
  ∑ z : Fin n → Bool, Real.negMulLog (coinLaw μ z)

end PrettyGoodShadow


