-- Prove2me | Definitions.Def_FractionalSpectralGP_chaosCoeff
-- name    : FractionalSpectralGP_chaosCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:55.221698+00:00
-- url     : https://prove2.me/theorems/905b2781-2920-43eb-bf7f-9ab5c881bf88
-- title:
--   Chaos coefficients $f_\alpha=E[FH_\alpha]/\alpha!$ of $F\in\mathcal W$
-- statement:
--   For $F$ in the white noise space, its chaos coefficients are
--
--   $$
--   f_\alpha=\frac{1}{\alpha!}\,E\big[F\,H_\alpha\big],\qquad\alpha\in\ell,
--   $$
--
--   so that $F=\sum_\alpha f_\alpha H_\alpha$ by (4.3). This is how an element of $\mathcal W$ (such as $W_\sigma(t)$ or an increment of $X_\sigma$) is read as a formal series, i.e. as an element of $S_{-1}$, on which the Wick product acts.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, §4, pp.10–11, (4.3)–(4.4)

import Mathlib
import Definitions.Def_FractionalSpectralGP_Omega
import Definitions.Def_FractionalSpectralGP_hermiteChaos
import Definitions.Def_FractionalSpectralGP_multiFactorial

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- The chaos coefficients `f_α = E[F H_α]/α!` of `F ∈ 𝒲`, so that `F = Σ_α f_α H_α`
(Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, §4, pp.10–11, (4.3)–(4.4)).

**Formalization Note.** This is how an element of the white noise space is read as a formal
series `Σ f_α H_α`, i.e. as an element of `S_{−1}`. Complex-valued `F` give complex coefficients. -/
noncomputable def chaosCoeff (P : Measure Omega) (ι : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 P) (h : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ)))
    (F : Lp ℂ 2 P) (α : ℕ →₀ ℕ) : ℂ :=
  ((multiFactorial α : ℂ))⁻¹ * ∫ ω, (F : Omega → ℂ) ω * (hermiteChaos P ι h α ω : ℂ) ∂P

end FractionalSpectralGP


