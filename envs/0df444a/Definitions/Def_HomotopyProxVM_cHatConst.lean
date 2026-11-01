-- Prove2me | Definitions.Def_HomotopyProxVM_cHatConst
-- name    : HomotopyProxVM_cHatConst
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:57.639495+00:00
-- url     : https://prove2.me/theorems/39e56e0d-7a0c-4759-aa8e-d5a75cc5712a
-- title:
--   The constant $\hat C$ of Theorem 4 (corrected)
-- statement:
--   With $b=L_g+\|\xi^0\|_2$, the constant of the last claim of Theorem 4 is taken to be
--
--   $$
--   \hat C:=C+\frac{(1-\tau_0)\,b}{\tau_0\mu_f}.
--   $$
--
--   **Formalization Note** The paper prints $\hat C:=C+\frac{(1-\tau_0)\omega(L_g+\|\xi^0\|_2)}{\tau_0^3\mu_f}$, and the claim is false with that constant. For $p=1$, $f(x)=(x-5/2)^2/2$, $g(x)=|x|/2$, $m=L=H_k=10/9$, $\tau_0=1/2$, $x^0=0$, $\xi^0=-1/2$, one has $\omega=1/10$, $C=3$, $\sigma=4/31$, printed $\hat C=17/5$ and $x^\star=2$, while exact arithmetic gives $|x^5-x^\star|\approx1.2307\cdot10^{-4}>1.2161\cdot10^{-4}\approx\hat C\sigma^5$. The constant here is what (51) gives at $\hat\tau=1$, using $1/\tau_k-1=\frac{1-\tau_0}{\tau_0}\sigma^k$.
-- source:
--   Tran-Dinh, Liang & Toh, A New Homotopy Proximal Variable-Metric Framework for Composite Convex Minimization, arXiv:1812.05243v1, Theorem 4, p.9, corrected; proof on p.27

import Mathlib

namespace HomotopyProxVM

/-- The constant `Ĉ` of the last claim of Theorem 4, **as corrected**:
`Ĉ := C + (1 − τ₀)(L_g + ‖ξ⁰‖₂) / (τ₀ μ_f)`, with `b = L_g + ‖ξ⁰‖₂`
(Tran-Dinh, Liang & Toh, arXiv:1812.05243v1, Theorem 4, p.9; the proof is on p.27).

**Formalization Note.** The paper prints `Ĉ := C + (1 − τ₀) ω (L_g + ‖ξ⁰‖₂) / (τ₀³ μ_f)`, and the
last claim of Theorem 4 is false with that constant. For `p = 1`, `f(x) = (x − 5/2)²/2`,
`g(x) = |x|/2`, `m = L = H_k = 10/9`, `τ₀ = 1/2`, `x⁰ = 0`, `ξ⁰ = −1/2`, one has `ω = 1/10`, `C = 3`,
`σ = 4/31`, printed `Ĉ = 17/5`, `x⋆ = 2`, and `|x⁵ − x⋆| ≈ 1.2307·10⁻⁴ > 1.2161·10⁻⁴ ≈ Ĉσ⁵`.
The constant here is what (51) gives with `τ̂ = 1` and `1/τ_k − 1 = ((1 − τ₀)/τ₀) σᵏ`. -/
noncomputable def cHatConst (C τ₀ b μ : ℝ) : ℝ :=
  C + (1 - τ₀) * b / (τ₀ * μ)

end HomotopyProxVM


