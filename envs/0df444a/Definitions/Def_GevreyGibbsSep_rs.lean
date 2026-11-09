-- Prove2me | Definitions.Def_GevreyGibbsSep_rs
-- name    : GevreyGibbsSep_rs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:50.270619+00:00
-- url     : https://prove2.me/theorems/103c2811-5434-4097-a579-50d503ba91af
-- title:
--   The constant $\mathfrak r_s$ of Eq. (B38)
-- statement:
--   With $t=1/(s-1)$, $Z_s=\int_{-1}^1\psi_s$,
--   $$r_1=\min\Big\{\frac{1}{8(t+1)4^s},\ \frac{\big(t\,2^{-(t+1)}\big)^{1/t}}{16(t+1)}\Big\},\qquad q_s=\max\{4,\ 2^{t+2}t\},$$
--   the constant is $\mathfrak r_s=\min\{r_1,\ Z_s/(e^2q_s)\}$. It depends only on $s$, and $\mathfrak r_s\le1/32$ (Remark B.4).
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Theorem B.1, Eq. (B38), p.41

import Mathlib
import Definitions.Def_GevreyGibbsSep_psiS

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The constant `r_s := min{r₁, Z_s/(e² q_s)}` of Eq. (B38), p.41 of arXiv:2608.24527 (sha256
d4fd40eb…), with `t = 1/(s − 1)`, `r₁ = min{1/(8(t + 1)4^s), (t 2^{−(t+1)})^{1/t}/(16(t + 1))}`,
`q_s = max{4, 2^{t+2} t}` and `Z_s = ∫_{−1}^1 ψ_s`. -/
noncomputable def rs (s : ℝ) : ℝ :=
  let t := 1 / (s - 1)
  let r1 := min (1 / (8 * (t + 1) * 4 ^ s)) ((t * 2 ^ (-(t + 1))) ^ (1 / t) / (16 * (t + 1)))
  let qs := max 4 (2 ^ (t + 2) * t)
  let Zs := ∫ y in (-1 : ℝ)..1, psiS s y
  min r1 (Zs / (Real.exp 2 * qs))

end GevreyGibbsSep


