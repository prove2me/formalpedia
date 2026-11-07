-- Prove2me | Definitions.Def_GeoSemialgCSP_unifAvg
-- name    : GeoSemialgCSP_unifAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:46:58.399032+00:00
-- url     : https://prove2.me/theorems/02d52050-e92f-41b1-af7a-6c5fb01af41c
-- title:
--   Uniform average
-- statement:
--   For a function $g$ on a finite set $\Omega$, $\mathbb E g(Z)=|\Omega|^{-1}\sum_{\omega\in\Omega}g(\omega)$ for $Z$ uniform on $\Omega$. Influences and the means in Sections 5 and 8 are computed under the uniform product measure on $[M]^R$.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §5, p.14 (PDF p.15); §8, p.22 (PDF p.23)

import Mathlib

namespace GeoSemialgCSP

/-- **Uniform average.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §5, printed p.14 (PDF p.15), and §8, printed p.22 (PDF p.23):
"All influences are computed under the uniform product measure on `[M]^R`"; `E` for `Z` uniform. -/
noncomputable def unifAvg {Ω : Type*} [Fintype Ω] (g : Ω → ℝ) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, g ω

end GeoSemialgCSP


