-- Prove2me | Definitions.Def_FreeOrderEPTAS_delta
-- name    : FreeOrderEPTAS_delta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:37.878643+00:00
-- url     : https://prove2.me/theorems/67649903-ea1c-4188-bc41-dc1ce6adc10f
-- title:
--   The explicit parameter $\delta$
-- statement:
--   The parameter $\delta=2^{-r}$, with
--   $$r=\big(8(mD+1)(\lceil1/\epsilon\rceil+1)\big)^2.$$
--   So $1/\delta$ is an integer and $\delta$ depends on $(\epsilon,m,D)$ only. It replaces the choice $\delta=(\epsilon^3/(32mD\psi^{2/3}))^3$ of p.12, which depends on an unspecified constant $\psi$ and assumes that $1/\delta$ is an integer.
--
--   The milestone `delta_calibration` states inequality (9) for this value.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §2.5, p.12

import Mathlib

namespace FreeOrderEPTAS

/-- The exponent of the explicit choice `δ = 2^{-r}` of §2.5 (arXiv:2007.13121v3, p.12):
`r = (8 (mD + 1)(⌈1/ϵ⌉ + 1))²`.

**Formalization Note.** The paper picks `δ = (ϵ³/(32mDψ^{2/3}))³`, assuming w.l.o.g. that `1/δ` is
an integer, for an unspecified constant `ψ`. This `r` is an explicit function of `(ϵ, m, D)`: it
makes `1/δ` an integer and gives inequality (9), which is `FreeOrderEPTAS.delta_calibration`. -/
noncomputable def calib (ϵ : ℝ) (m D : ℕ) : ℕ :=
  (8 * (m * D + 1) * (⌈1 / ϵ⌉₊ + 1)) ^ 2

/-- The parameter `δ = 2^{-r}`, with `1/δ = 2^r ∈ ℕ`. -/
noncomputable def delta (ϵ : ℝ) (m D : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ calib ϵ m D

end FreeOrderEPTAS


