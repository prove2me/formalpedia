-- Prove2me | Definitions.Def_FractionalSpectralGP_ftInd
-- name    : FractionalSpectralGP_ftInd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:55.316288+00:00
-- url     : https://prove2.me/theorems/213c11b0-891a-4165-ba7a-4bfd71469bb9
-- title:
--   $f_t(u)=\int_0^te^{iux}\,dx$, the Fourier transform of $1_{[0,t]}$
-- statement:
--   For $t\in\mathbb R$ let
--
--   $$
--   f_t(u)=\int_0^te^{iux}\,dx=\widehat{1_{[0,t]}}(u),
--   $$
--
--   with the oriented integral, so that for $t<0$ it is the transform of $-1_{[t,0]}$. Then $f_t(0)=t$ and, for $u\ne0$, $f_t(u)=-i\,\dfrac{e^{itu}-1}{u}=-i\chi_t(u)$.
--
--   $Q_\sigma1_{[0,t]}$ is the extended operator of Proposition 5.4 evaluated at $f_t$; this defines the process $X_\sigma(t)$.
--
--   **Formalization Note** The paper approximates $\chi_t$ on p.16, but the expansion (6.2) and the derivative (6.4) hold for $f_t$; with $\chi_t$ every coefficient would carry an extra factor $i$.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, §6, (6.2), p.21; §5, p.16

import Mathlib

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- The Fourier transform of the indicator of `[0, t]`, `f_t(u) = ∫₀ᵗ e^{iux} dx`
(Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, §6, (6.2), p.21: the function at which the extended `Q_σ` is evaluated to
define `X_σ(t) = Q̃_σ(1_{[0,t]})`).

**Formalization Note.** The integral is oriented, so for `t < 0` this is the transform of
`−1_{[t,0]}`, as (6.2) requires for all real `t`. `f_t(0) = t`, and for `u ≠ 0`,
`f_t(u) = −i (e^{itu} − 1)/u = −i χ_t(u)`; the printed quotient `χ_t` is not used here because
(6.2) and (6.4) hold for `f_t` and would be off by the factor `i` for `χ_t`. -/
noncomputable def ftInd (t : ℝ) (u : ℝ) : ℂ :=
  ∫ x in (0:ℝ)..t, Complex.exp (Complex.I * u * x)

end FractionalSpectralGP


