-- Prove2me | Definitions.Def_RandomLPIPM_IsLogLipschitz
-- name    : RandomLPIPM_IsLogLipschitz
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:08:56.183304+00:00
-- url     : https://prove2.me/theorems/38bf5902-7e78-4bd1-8f51-598853a1f1dd
-- title:
--   Definition 9.1: the central path is $C$-Lipschitz in logarithmic coordinates
-- statement:
--   Let $0<\mu_{\mathrm{end}}\le\mu_{\mathrm{start}}$. The central path of (LP) is **$C$-Lipschitz in logarithmic coordinates on $[\mu_{\mathrm{end}},\mu_{\mathrm{start}}]$** if
--   $$\Big\|\frac{d\log x(\mu)}{d\log\mu}\Big\|_\infty\le C\qquad\text{for all }\mu\in[\mu_{\mathrm{end}},\mu_{\mathrm{start}}].$$
--   Here, for each coordinate $i$, $\frac{d\log x(\mu)_i}{d\log\mu}$ is the derivative of $t\mapsto\log x(e^t)_i$ at $t=\log\mu$.
--
--   This constant controls how far any coordinate of the central path moves when $\mu$ changes by a given factor, and so the length of the outer steps of Algorithm 1.
--
--   **Formalization Note** The derivative is asserted to exist (an existential derivative with a bound), so a non-differentiable path cannot satisfy the bound vacuously. The central path is smooth (p.7), so this adds nothing.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Definition 9.1, p.76

import Mathlib
import Definitions.Def_RandomLPIPM_centralX

open Matrix

namespace RandomLPIPM

/-- **Definition 9.1: the central path is `C`-Lipschitz in logarithmic coordinates on
`[μ_end, μ_start]`.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Definition 9.1, p.76: "`‖d log x(μ) / d log μ‖_∞ ≤ C` for all
`μ ∈ [μ_end, μ_start]`".

For every `μ` in the interval and every coordinate `i`, the function `t ↦ log x(eᵗ)ᵢ` is
differentiable at `t = log μ` with derivative of absolute value at most `C`.

**Formalization Note.** Written with `HasDerivAt` and an existential derivative instead of `deriv`,
so that a non-differentiable path cannot meet the bound through the junk value `0` of `deriv`. The
central path is smooth (p.7, implicit function theorem), so nothing is added. -/
def IsLogLipschitz {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (b : Fin d → ℝ) (c : Fin n → ℝ)
    (C μend μstart : ℝ) : Prop :=
  ∀ μ ∈ Set.Icc μend μstart, ∀ i : Fin n, ∃ g : ℝ,
    HasDerivAt (fun t => Real.log (centralX A b c (Real.exp t) i)) g (Real.log μ) ∧ |g| ≤ C

end RandomLPIPM


