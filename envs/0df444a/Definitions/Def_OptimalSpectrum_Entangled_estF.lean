-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_estF
-- name    : OptimalSpectrum_Entangled_estF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:44.185537+00:00
-- url     : https://prove2.me/theorems/ad2c3482-25b6-4075-a4b5-ffc5d63f4295
-- title:
--   Polynomial moment estimate $\widehat F_p=\sum_{m=0}^K p_m\widehat M_m$
-- statement:
--   Given real random variables $\widehat M_1,\dots,\widehat M_K$ (estimates of the moments $\sum_i\alpha_i^m$) and $\widehat M_0=d$, the estimate of $\sum_i p(\alpha_i)$ for a polynomial $p(x)=\sum_{m=0}^Kp_mx^m$ is
--
--   $$\widehat F_p=\sum_{m=0}^K p_m\widehat M_m .$$
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, §6 Setup, p. 13 (PDF p. 15)

import Mathlib

namespace OptimalSpectrum.Entangled

/-- **Polynomial moment estimate `F̂_p`.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, §6 Setup, printed p. 13 (PDF p. 15): "Let M̂₁, …, M̂_K be unbiased real estimates of the
monomial moments ∑_i α_i^m, with finite variances, and set M̂₀ = d. … For a polynomial
p(x) = ∑_(m=0)^K p_m x^m, define F̂_p = ∑_(m=0)^K p_m M̂_m."

Given random variables `M̂_m : Ω → ℝ` (`1 ≤ m ≤ K`), `estF d K M̂ p ω = p₀ d + ∑_(m=1)^K p_m M̂_m(ω)`.

**Formalization Note.** Only `M̂_1, …, M̂_K` are read; `M̂₀ = d` is built in. -/
noncomputable def estF {Ω : Type*} (d K : ℕ) (Mhat : ℕ → Ω → ℝ) (p : Polynomial ℝ) (ω : Ω) : ℝ :=
  ∑ m ∈ Finset.range (K + 1), p.coeff m * (if m = 0 then (d : ℝ) else Mhat m ω)

end OptimalSpectrum.Entangled


