-- Prove2me | Definitions.Def_GeoSemialgCSP_inflV
-- name    : GeoSemialgCSP_inflV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:49:35.82525+00:00
-- url     : https://prove2.me/theorems/f58004b4-221c-4bcf-a053-5e420df2aef2
-- title:
--   Total vector influence
-- statement:
--   For $F:W^R\to\mathbb R^q$ and $Z$ uniform, the **total vector influence** of coordinate $r$ is
--   $$\mathrm{Inf}_r(F)=\mathbb E\bigl\|F(Z)-\mathbb E[F(Z)\mid Z_{-r}]\bigr\|_2^2=\sum_{a\in[q]}\mathrm{Inf}_r(F_a).$$
--   $F$ is $\tau$-pseudorandom if $\mathrm{Inf}_r(F)\le\tau$ for every $r$.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §8, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_GeoSemialgCSP_infl

namespace GeoSemialgCSP

/-- **Total vector influence.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §8, printed p.22 (PDF p.23):
`Inf_i(H) = E‖H(Z) − E[H(Z) | Z_{−i}]‖₂²` for `H : [M]^R → ℝ^q`, i.e. the sum of the influences of
its `q` components. -/
noncomputable def inflV {W : Type*} [Fintype W] {R q : ℕ} (F : (Fin R → W) → Fin q → ℝ)
    (r : Fin R) : ℝ :=
  ∑ a : Fin q, infl (fun z => F z a) r

end GeoSemialgCSP


