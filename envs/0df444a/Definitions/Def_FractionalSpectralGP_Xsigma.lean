-- Prove2me | Definitions.Def_FractionalSpectralGP_Xsigma
-- name    : FractionalSpectralGP_Xsigma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:29:43.105181+00:00
-- url     : https://prove2.me/theorems/ee9cff0e-2401-466b-8aed-cdf297465c80
-- title:
--   The process $X_\sigma(t)=\widetilde{Q_\sigma(1_{[0,t]})}$
-- statement:
--   For a spectral setting, a real orthonormal basis $(h_n)$, the white noise measure $P$ and the isometry $f\mapsto\widetilde f$,
--
--   $$
--   X_\sigma(t)=\widetilde{Q_\sigma(1_{[0,t]})}\in\mathcal W,\qquad t\in\mathbb R,
--   $$
--
--   where $Q_\sigma1_{[0,t]}$ is the extended operator of Proposition 5.4 at $f_t=\widehat{1_{[0,t]}}$. This is the Gaussian process with stationary increments whose spectral measure is $\sigma$; Theorem 6.2 shows it is differentiable in $\mathcal W$ with derivative $W_\sigma$.
--
--   **Formalization Note** $f_t(u)=\int_0^te^{iux}dx$ is an oriented integral, so negative $t$ is covered as in (6.2).
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, (6.2), p.21; §1, p.5

import Mathlib
import Definitions.Def_FractionalSpectralGP_SpectralSetting
import Definitions.Def_FractionalSpectralGP_QsigmaExt
import Definitions.Def_FractionalSpectralGP_ftInd
import Definitions.Def_FractionalSpectralGP_Omega

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- The Gaussian process `X_σ(t) = Q̃_σ(1_{[0,t]})` (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, (6.2), p.21; §1, p.5): the
image under `f ↦ f̃` of the extended operator `Q_σ` at the indicator of `[0, t]`.

**Formalization Note.** `Q_σ 1_{[0,t]}` is the extension of Proposition 5.4 at
`f_t(u) = ∫₀ᵗ e^{iux} dx = 1̂_{[0,t]}(u)` (`ftInd`), an oriented integral, so `t < 0` is covered.
`P` and `ι` are the white noise measure and the isometry `f ↦ f̃`, passed as parameters. -/
noncomputable def Xsigma (S : SpectralSetting) (h : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ))) (P : Measure Omega)
    (ι : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 P) (t : ℝ) : Lp ℂ 2 P :=
  ι (QsigmaExt S h (ftInd t))

end FractionalSpectralGP


