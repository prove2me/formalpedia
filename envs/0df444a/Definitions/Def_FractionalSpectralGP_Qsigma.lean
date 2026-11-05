-- Prove2me | Definitions.Def_FractionalSpectralGP_Qsigma
-- name    : FractionalSpectralGP_Qsigma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:27:10.385818+00:00
-- url     : https://prove2.me/theorems/f39402a2-9609-4134-84a9-23171630f860
-- title:
--   The operator $Q_\sigma(\psi)=\widehat\psi(T)h_0$ on Schwartz functions
-- statement:
--   For a Schwartz function $\psi$,
--
--   $$
--   Q_\sigma(\psi)=\widehat\psi(T)\,h_0\in L^2(\mathbb R,dx),
--   $$
--
--   where $\widehat\psi(T)$ is the continuous functional calculus of the self-adjoint operator $T=WM_uW^*$ applied to the continuous function $\widehat\psi$.
--
--   $Q_\sigma$ is the counterpart, for singular $\sigma$, of the convolution operator with $\sqrt m$ used when $\sigma$ has a density $m$; $X_\sigma$ is built from it.
--
--   **Formalization Note** The functional calculus is applied to $z\mapsto\widehat\psi(\operatorname{Re}z)$, which is $\widehat\psi$ on the real spectrum of $T$. Schwartz functions are complex-valued (the paper's $\mathcal S$ is real-valued). The expansion (5.2) is a theorem (Lemma 5.1), not the definition.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, §5, p.12

import Mathlib
import Definitions.Def_FractionalSpectralGP_SpectralSetting
import Definitions.Def_FractionalSpectralGP_paperFourier
import Definitions.Def_FractionalSpectralGP_opT

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- The operator `Q_σ(ψ) = ψ̂(T) h₀` for a Schwartz function `ψ`
(Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, §5, p.12, after (5.1)).

**Formalization Note.** `ψ̂(T)` is the continuous functional calculus (`cfc`) of the self-adjoint
operator `T`, applied to the continuous function `z ↦ ψ̂(Re z)` (on the real spectrum of `T` this
is `ψ̂`). Schwartz functions are complex-valued (the paper's `𝒮` is real-valued; complex
coefficients generalize it). -/
noncomputable def Qsigma (S : SpectralSetting) (h : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ))) (ψ : 𝓢(ℝ, ℂ)) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  cfc (fun z : ℂ => paperFourier ψ z.re) (opT S h) (h 0)

end FractionalSpectralGP


