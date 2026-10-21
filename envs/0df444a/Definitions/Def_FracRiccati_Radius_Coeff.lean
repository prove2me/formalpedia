-- Prove2me | Definitions.Def_FracRiccati_Radius_Coeff
-- name    : FracRiccati_Radius_Coeff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:22.718359+00:00
-- url     : https://prove2.me/theorems/749f78af-c6ce-4342-a117-0773f4a651cb
-- title:
--   (3.19)–(3.21), p. 8 — coefficients (A_λ,μ,ν) of the fractional power-series solution, and the Hadamard radius R_ψ
-- statement:
--   This file fixes the two objects every statement of the mission is about.
--
--   **The fractional Riccati equation.** For $\alpha\in(0,2]$ and complex parameters $\lambda,\mu,\nu$, Callegaro, Grasselli and Pagès look for a solution of the fractional Riccati equation $D^\alpha\psi=\lambda\psi^2+\mu\psi+\nu$ with zero initial condition as a fractional power series
--   $$\psi_{\lambda,\mu,\nu}(t)=\sum_{k\ge0}a_k\,t^{k\alpha}. \qquad (3.17)$$
--   Identifying coefficients gives the discrete convolution equation $(A_{\lambda,\mu,\nu})$:
--
--   1. **Coefficients.** $a_0=0$, $a_1=\dfrac{\nu}{\Gamma(\alpha+1)}$, and for every $k\ge1$
--   $$a_{k+1}=\big(\lambda\,a^{*2}_k+\mu\,a_k\big)\,\frac{\Gamma(\alpha k+1)}{\Gamma(\alpha k+\alpha+1)},\qquad a^{*2}_k=\sum_{\ell=1}^{k-1}a_\ell\,a_{k-\ell}, \qquad (3.19),\ (3.20)$$
--   so that $a^{*2}_1=0$. The sequence is uniquely determined, since $a_{k+1}$ only involves $a_1,\dots,a_k$.
--   2. **Convergence radius.** The radius of the fractional power series is given by Hadamard's formula
--   $$R_\psi=\liminf_{k}\,|a_k|^{-\frac{1}{\alpha k}}\in[0,+\infty]. \qquad (3.21)$$
--
--   The coefficient map $(\alpha,\lambda,\mu,\nu)\mapsto(a_k)_k$ and the radius are the objects of Theorem 3.3 and of all the coefficient bounds of Appendix B.
--
--   **Formalization Note** The sequence is indexed by $\mathbb N$ with $a_0=0$; the recursion is written for the index $j+2=(j+1)+1$ and the convolution runs over $\ell\in\{1,\dots,j\}$ (`Finset.Ico 1 (j+1)`). The Gamma factors are real (`Real.Gamma`) and cast to $\mathbb C$. The radius is computed in $[0,\infty]$ (`ℝ≥0∞`) as the `liminf` along `atTop` of $\|a_k\|^{-1/(\alpha k)}$, where $0^{-x}=+\infty$ for $x>0$, so vanishing coefficients do not lower the radius, as in Hadamard's formula. At $k=0$ the exponent $-1/(\alpha\cdot0)$ is $0$ in Lean and the term is $1$; a single term does not affect a `liminf`. The radius takes an arbitrary sequence and $\alpha$ as arguments.
-- source:
--   Callegaro, Grasselli, Pagès, Fast Hybrid Schemes for Fractional Riccati Equations (Rough is not so Tough), arXiv:1805.12587v4, p. 8, (3.17), (3.19), (3.20), (3.21)

import Mathlib

namespace FracRiccati.Radius

open scoped ENNReal

/-- The coefficients `(a_k)_{k ≥ 0}` of the fractional power series `ψ(t) = Σ_k a_k t^{kα}`
solving the fractional Riccati equation with zero initial condition, given by the recursion
`(A_{λ,μ,ν})` of (3.19) together with the convolution convention (3.20):
`a_0 = 0`, `a_1 = ν / Γ(α + 1)` and, for `k ≥ 1`,
`a_{k+1} = (λ Σ_{ℓ=1}^{k-1} a_ℓ a_{k-ℓ} + μ a_k) Γ(αk + 1) / Γ(αk + α + 1)`.
Here the recursion index is `k = j + 1` for `j : ℕ`. -/
noncomputable def coeff (α : ℝ) (lam mu nu : ℂ) : ℕ → ℂ
  | 0 => 0
  | 1 => nu / (Real.Gamma (α + 1) : ℂ)
  | j + 2 =>
      (lam * ∑ ℓ ∈ (Finset.Ico 1 (j + 1)).attach,
          coeff α lam mu nu ℓ.1 * coeff α lam mu nu (j + 1 - ℓ.1)
        + mu * coeff α lam mu nu (j + 1))
      * ((Real.Gamma (α * ((j + 1 : ℕ) : ℝ) + 1) /
          Real.Gamma (α * ((j + 1 : ℕ) : ℝ) + α + 1) : ℝ) : ℂ)
termination_by k => k
decreasing_by
  all_goals
    first
    | (have := (Finset.mem_Ico.mp ℓ.2).2; omega)
    | omega

/-- The convergence radius (3.21) of the fractional power series `Σ_k a_k t^{kα}`, by
Hadamard's formula `R = liminf_k |a_k|^{-1/(αk)} ∈ [0, +∞]`, computed in `ℝ≥0∞`
(where `0 ^ (-x) = ⊤` for `x > 0`). -/
noncomputable def radius (α : ℝ) (a : ℕ → ℂ) : ℝ≥0∞ :=
  Filter.liminf (fun k : ℕ => ((‖a k‖₊ : ℝ≥0∞) ^ (-(1 / (α * (k : ℝ))) : ℝ))) Filter.atTop

end FracRiccati.Radius


