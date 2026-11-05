-- Prove2me | Definitions.Def_FractionalSpectralGP_Wsigma
-- name    : FractionalSpectralGP_Wsigma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:33.392093+00:00
-- url     : https://prove2.me/theorems/f7ad4bad-7b6d-4f52-b157-cc120befaa85
-- title:
--   The derivative process $W_\sigma(t)=\sum_n\widehat\sigma(t-\lambda_n)Z_n$ (6.4)
-- statement:
--   With the notation of the spectral setting and $Z_n=\widetilde{h_n}$,
--
--   $$
--   W_\sigma(t)=\sum_{n=0}^{\infty}\widehat\sigma(t-\lambda_n)\,Z_n\in\mathcal W,\qquad t\in\mathbb R .
--   $$
--
--   By (3.1) the coefficients are square-summable with sum $1$, so the series converges in $\mathcal W$; Theorem 6.2 identifies $W_\sigma$ as the derivative of $X_\sigma$, and $W_\sigma$ is the integrator of the Wick–Itô integral of Theorem 7.1.
--
--   **Formalization Note** The series is an unconditional sum in $L^2(P;\mathbb C)$ (`tsum`); Theorem 6.2 states that it converges.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, (6.4), p.22

import Mathlib
import Definitions.Def_FractionalSpectralGP_SpectralSetting
import Definitions.Def_FractionalSpectralGP_sigmaHat
import Definitions.Def_FractionalSpectralGP_Omega
import Definitions.Def_FractionalSpectralGP_Zn

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- The derivative process `W_σ(t) = Σ_{n ≥ 0} σ̂(t − λ_n) Z_n` (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, (6.4), p.22),
an element of the white noise space `𝒲 = L²(P)`.

**Formalization Note.** The series is a `tsum` in `L²(P; ℂ)`; Theorem 6.2 (`theorem_6_2`) states
that it converges there (unconditionally, by (3.1)), so the value is never a junk `0`. -/
noncomputable def Wsigma (S : SpectralSetting) (h : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ))) (P : Measure Omega)
    (ι : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 P) (t : ℝ) : Lp ℂ 2 P :=
  ∑' n, sigmaHat S.σ (t - S.lam n) • Zn P ι h n

end FractionalSpectralGP


