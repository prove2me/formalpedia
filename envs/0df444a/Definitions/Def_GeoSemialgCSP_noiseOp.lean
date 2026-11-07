-- Prove2me | Definitions.Def_GeoSemialgCSP_noiseOp
-- name    : GeoSemialgCSP_noiseOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:34.358203+00:00
-- url     : https://prove2.me/theorems/a9e86c61-ef11-41a7-b9f8-c57b96c31ba7
-- title:
--   Noise operator $T_\sigma$
-- statement:
--   For $g:W^R\to\mathbb R$, the noise operator is
--   $$(T_\sigma g)(z)=\mathbb E\,g(\tilde z),$$
--   where $\tilde z$ is the noisy copy of $z$ that keeps each coordinate with probability $\sigma$ and otherwise resamples it uniformly.
--
--   It preserves means, maps $[0,1]$-valued functions to $[0,1]$-valued functions, and does not increase influences.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_GeoSemialgCSP_noiseK

namespace GeoSemialgCSP

/-- **Noise operator on scalar functions.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3, printed p.8 (PDF p.9):
`(T_σ g)(z) = E_{z̃} g(z̃)`, where `z̃` keeps each coordinate of `z` with probability `σ` and
otherwise resamples it uniformly from `W`. -/
noncomputable def noiseOp {W : Type*} [Fintype W] {R : ℕ} (σ : ℝ) (g : (Fin R → W) → ℝ)
    (z : Fin R → W) : ℝ :=
  ∑ z', noiseK σ z z' * g z'

end GeoSemialgCSP


