-- Prove2me | Definitions.Def_SecondBestBT_lambdaGen
-- name    : SecondBestBT_lambdaGen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:03.163698+00:00
-- url     : https://prove2.me/theorems/7f496751-a0b1-4c1e-86d5-f785b500eb7e
-- title:
--   Generalized budget-balance discriminant $\Lambda_{\mathrm{gen}}(x)$
-- statement:
--   For priors $F_S,F_B$ on $[0,1]$ and an allocation $x$, the **generalized budget-balance discriminant** is
--   $$
--   \Lambda^{F_S,F_B}_{\mathrm{gen}}(x)=\int_{[0,1]}\Big(b\,x_B(b)-\int_0^b x_B(t)\,dt\Big)dF_B(b)-\int_{[0,1]}\Big(s\,x_S(s)+\int_s^1 x_S(t)\,dt\Big)dF_S(s).
--   $$
--   For monotone interim allocations it is the largest expected budget surplus achievable under BIC and interim IR.
--
--   **Formalization Note** The inner integrals are against Lebesgue measure on $[0,b]$ and $[s,1]$.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 3, p.5

import Mathlib
import Definitions.Def_SecondBestBT_interimB
import Definitions.Def_SecondBestBT_interimS

open MeasureTheory

namespace SecondBestBT

/-- The generalized budget-balance discriminant (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version
sha256 17184930…, Section 3, p.5):
`Λ_gen(x) = ∫ (b·x_B(b) − ∫₀^b x_B(t) dt) dF_B(b) − ∫ (s·x_S(s) + ∫ₛ¹ x_S(t) dt) dF_S(s)`.

**Formalization Note** The inner integrals are interval integrals against Lebesgue measure on
`[0, b]` and `[s, 1]`; the outer integrals are against the priors. The definition is used only for
priors on `[0, 1]` and allocations with values in `[0, 1]` on `[0, 1]²`, where every integrand is
bounded and measurable. -/
noncomputable def lambdaGen (μS μB : Measure ℝ) (x : ℝ × ℝ → ℝ) : ℝ :=
  (∫ b, (b * interimB μS x b - ∫ t in (0 : ℝ)..b, interimB μS x t) ∂μB) -
    ∫ s, (s * interimS μB x s + ∫ t in s..(1 : ℝ), interimS μB x t) ∂μS

end SecondBestBT


