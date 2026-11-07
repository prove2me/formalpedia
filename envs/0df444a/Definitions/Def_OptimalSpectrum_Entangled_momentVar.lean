-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_momentVar
-- name    : OptimalSpectrum_Entangled_momentVar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:19:44.510403+00:00
-- url     : https://prove2.me/theorems/494099f7-98e5-4ff1-b47e-b62394ddd8a2
-- title:
--   Moment estimate variance, Eq. (18): $\mathbb E\big(\widehat F_p-\sum_i p(\alpha_i)\big)^2$
-- statement:
--   For moment estimates $\widehat M_m$ of a spectrum $\alpha$ and a polynomial $p$,
--
--   $$\mathrm{Var}(\widehat F_p)=\mathbb E\Big[\Big(\widehat F_p-\sum_{i=1}^d p(\alpha_i)\Big)^2\Big].$$
--
--   Under unbiasedness $\mathbb E\widehat F_p=\sum_ip(\alpha_i)$, this is the variance; the paper uses it in this form (Eq. (18)).
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, §6 Setup, Eq. (18), p. 13 (PDF p. 15)

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_estF

open MeasureTheory

namespace OptimalSpectrum.Entangled

/-- **Variance of a moment estimate, Eq. (18).**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, §6 Setup, Eq. (18), printed p. 13 (PDF p. 15): "Unbiasedness gives E F̂_p = ∑_i p(α_i), and
therefore Var(F̂_p) = E[(F̂_p − ∑_(i=1)^d p(α_i))²]."

**Formalization Note.** Defined as the right side of (18), the second moment about `∑ᵢ p(αᵢ)`; under
the unbiasedness hypothesis of the statements that use it, this is the variance. The estimates have
finite second moments there, so the integral is not a junk value. -/
noncomputable def momentVar {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (d K : ℕ)
    (Mhat : ℕ → Ω → ℝ) (α : Fin d → ℝ) (p : Polynomial ℝ) : ℝ :=
  ∫ ω, (estF d K Mhat p ω - ∑ i, p.eval (α i)) ^ 2 ∂μ

end OptimalSpectrum.Entangled


