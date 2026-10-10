-- Prove2me | Definitions.Def_PriceQualityService_Uniform_Reduction
-- name    : PriceQualityService_Uniform_Reduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:48.755028+00:00
-- url     : https://prove2.me/theorems/e2c8af4f-cafd-4ed8-90b1-be76e28fb886
-- title:
--   The quadratic exponent, $G_i$, $A_i$ and $y$ of the proof of Theorem 3
-- statement:
--   Fix the parameters $\alpha_i,a_i,b_i,c_i,s_i$ of the products $i\in\mathcal N$ and let $t$ be a common (uniform) service duration and $r$ a real number.
--
--   1. **Exponent.** $\varphi_i(t)=\dfrac{b_i^2t^2}{4c_i}+\Big(s_i-a_i+\dfrac{\alpha_ib_i}{2c_i}\Big)t+\dfrac{\alpha_i^2}{4c_i}$.
--   2. **$G_i$.** $G_i(r,t)=\exp\big(\varphi_i(t)-r-1\big)$, the summand of equation (24).
--   3. **$A_i$.** $A_i(t)=s_i-a_i+\dfrac{\alpha_ib_i}{2c_i}+\dfrac{tb_i^2}{2c_i}$, the derivative of $\varphi_i$ in $t$.
--   4. **$y$.** $y(t)=\sum_{i\in\mathcal N}\exp\big(\varphi_i(t)\big)$, the numerator of the right-hand side of (25).
--
--   In the paper's proof of Theorem 3 the total expected profit $r$ at a uniform duration $t$ is the root of
--   $$
--   r=\sum_{i\in\mathcal N}G_i(r,t),
--   $$
--   and these quantities enter its derivative in $t$ and the alternative proof through $y$.
--
--   **Formalization Note** These are plain real-valued functions of the parameters; the root $r$ itself is not defined here (statements quantify over a function $R$ with $R(t)=\sum_iG_i(R(t),t)$ for every $t$). Division by $c_i$ is Lean's total division; every theorem that uses these functions assumes $c_i>0$.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), pp. 29–30, Proof of Theorem 3, (24), (25)

import Mathlib

namespace PriceQualityService.Uniform

open Finset

/-- The quadratic exponent of product `i` at a common service duration `t` (Proof of Theorem 3,
(24)–(25), Wang, Ke & Cui, accepted manuscript (SSRN 3766191), pp. 29–30):
`b_i² t² / (4 c_i) + (s_i − a_i + α_i b_i / (2 c_i)) t + α_i² / (4 c_i)`. -/
noncomputable def exponent {N : ℕ} (α a b c s : Fin N → ℝ) (t : ℝ) (i : Fin N) : ℝ :=
  b i ^ 2 * t ^ 2 / (4 * c i) + (s i - a i + α i * b i / (2 * c i)) * t + α i ^ 2 / (4 * c i)

/-- The paper's `G_i = exp(b_i² t²/(4c_i) + (s_i − a_i + α_i b_i/(2c_i)) t + α_i²/(4c_i) − r − 1)`
(p. 29), as a function of `r` and `t`. -/
noncomputable def gTerm {N : ℕ} (α a b c s : Fin N → ℝ) (r t : ℝ) (i : Fin N) : ℝ :=
  Real.exp (exponent α a b c s t i - r - 1)

/-- The paper's `A_i = s_i − a_i + α_i b_i/(2c_i) + t b_i²/(2c_i)` (p. 29), the derivative of the
exponent of product `i` in `t`. -/
noncomputable def aTerm {N : ℕ} (α a b c s : Fin N → ℝ) (t : ℝ) (i : Fin N) : ℝ :=
  s i - a i + α i * b i / (2 * c i) + t * b i ^ 2 / (2 * c i)

/-- The paper's `y = ∑_{i ∈ 𝒩} exp(b_i² t²/(4c_i) + (s_i − a_i + α_i b_i/(2c_i)) t + α_i²/(4c_i))`
(p. 30), the numerator of the right-hand side of (25). -/
noncomputable def yTotal {N : ℕ} (α a b c s : Fin N → ℝ) (t : ℝ) : ℝ :=
  ∑ i, Real.exp (exponent α a b c s t i)

end PriceQualityService.Uniform


