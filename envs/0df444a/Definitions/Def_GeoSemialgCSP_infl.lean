-- Prove2me | Definitions.Def_GeoSemialgCSP_infl
-- name    : GeoSemialgCSP_infl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:33.94497+00:00
-- url     : https://prove2.me/theorems/cfbfa3fb-477c-411f-b813-419f281f0a91
-- title:
--   Influence of a coordinate
-- statement:
--   For $g:W^R\to\mathbb R$ under the uniform product measure, the **influence** of coordinate $r$ is
--   $$\mathrm{Inf}_r(g)=\mathbb E\Bigl[\mathrm{Var}\bigl(g\mid (z_{r'})_{r'\neq r}\bigr)\Bigr]=\mathbb E_z\Bigl[\Bigl(g(z)-\frac1{|W|}\sum_{w\in W}g(z_1,\dots,z_{r-1},w,z_{r+1},\dots,z_R)\Bigr)^2\Bigr],$$
--   the expected variance of $g$ when only coordinate $r$ is resampled. A function is $\tau$-pseudorandom if all its influences are at most $\tau$.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Eq. (1), p.8 (PDF p.9)

import Mathlib
import Definitions.Def_GeoSemialgCSP_unifAvg

namespace GeoSemialgCSP

/-- **Influence of a coordinate.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Eq. (1), printed p.8 (PDF p.9):
`Inf_r(g) = E[Var(g | (z_{r'})_{r' ≠ r})]`, the expected variance of `g` when only coordinate `r`
is resampled, under the uniform product measure on `W^R`.

**Formalization Note.** The conditional mean is the average of `g(z₁, …, w, …, z_R)` over
`w ∈ W` in coordinate `r`. -/
noncomputable def infl {W : Type*} [Fintype W] {R : ℕ} (g : (Fin R → W) → ℝ) (r : Fin R) : ℝ :=
  unifAvg (fun z => (g z - (Fintype.card W : ℝ)⁻¹ * ∑ w, g (Function.update z r w)) ^ 2)

end GeoSemialgCSP


