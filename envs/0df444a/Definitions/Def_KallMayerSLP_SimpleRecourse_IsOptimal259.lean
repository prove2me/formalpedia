-- Prove2me | Definitions.Def_KallMayerSLP_SimpleRecourse_IsOptimal259
-- name    : KallMayerSLP_SimpleRecourse_IsOptimal259
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:12:34.479398+00:00
-- url     : https://prove2.me/theorems/46d2b8a1-2d5b-4b52-8622-707f4ad34ea6
-- title:
--   Optimal solutions of the simple recourse problem (2.59)
-- statement:
--   For $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $c,t\in\mathbb R^n$ and a function $\Psi:\mathbb R\to\mathbb R$, consider
--
--   $$
--   \min\{c^{\mathrm T}x+\Psi(z)\}\quad\text{s.t.}\quad Ax=b,\quad t^{\mathrm T}x-z=0,\quad x\ge0. \tag{2.59}
--   $$
--
--   A pair $(x,z)$ is **optimal** if it is feasible and $c^{\mathrm T}x+\Psi(z)\le c^{\mathrm T}x'+\Psi(z')$ for every feasible $(x',z')$.
--
--   **Formalization Note** "min" is read as the set of minimizers; $\Psi$ is any real function (the expected MSRT function, or the expected SRT function (2.61)).
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, (2.59), p.241 (PDF 250)

import Mathlib

open Matrix

namespace KallMayerSLP.SimpleRecourse

/-- **Optimal solutions of the simple recourse problem (2.59).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, (2.59), p.241 (PDF 250):
`min{cᵀx + Ψ(z)}` subject to `Ax = b`, `tᵀx − z = 0`, `x ≥ 0`.
`(x, z)` is optimal if it is feasible and its objective value is at most that of every feasible
`(x', z')`.

**Formalization Note.** `x ∈ ℝⁿ` as `Fin n → ℝ`, `A ∈ ℝ^{m×n}`, `Ψ : ℝ → ℝ` any real function
(the expected MSRT function, or the expected SRT function of (2.61)); "min" is read as the set of
minimizers. -/
def IsOptimal259 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c t : Fin n → ℝ)
    (Ψ : ℝ → ℝ) (x : Fin n → ℝ) (z : ℝ) : Prop :=
  (A *ᵥ x = b ∧ t ⬝ᵥ x - z = 0 ∧ ∀ j, 0 ≤ x j) ∧
    ∀ (x' : Fin n → ℝ) (z' : ℝ), A *ᵥ x' = b → t ⬝ᵥ x' - z' = 0 → (∀ j, 0 ≤ x' j) →
      c ⬝ᵥ x + Ψ z ≤ c ⬝ᵥ x' + Ψ z'

end KallMayerSLP.SimpleRecourse


