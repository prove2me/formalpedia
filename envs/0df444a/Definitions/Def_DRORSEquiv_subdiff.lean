-- Prove2me | Definitions.Def_DRORSEquiv_subdiff
-- name    : DRORSEquiv_subdiff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:34:35.483986+00:00
-- url     : https://prove2.me/theorems/f00e9919-237e-4d5f-ae7d-2c2fc26f5fd6
-- title:
--   Subdifferential $\partial\varphi(\tau)$ of a function $\mathbb R\to[0,\infty]$
-- statement:
--   For $\varphi:\mathbb R\to[0,\infty]$ and $\tau\in\mathbb R$, a number $\alpha$ is a **subgradient** of $\varphi$ at $\tau$ when $\varphi(\tau)<\infty$ and
--
--   $$\varphi(\tau')\ge\varphi(\tau)+\alpha(\tau'-\tau)\qquad\text{for all }\tau'\in\mathbb R .$$
--
--   The **subdifferential** $\partial\varphi(\tau)$ is the set of subgradients. It is used for $\partial\kappa(\tau)$ in Theorem 1.
--
--   **Formalization Note** Convex-analysis convention: $\partial\varphi(\tau)=\emptyset$ where $\varphi(\tau)=\infty$, and points $\tau'$ with $\varphi(\tau')=\infty$ impose no constraint. The paper's inequality ranges over $\tau'\ge Z_0$; for $\varphi=\kappa$ this is the same set because $\kappa=\infty$ below $Z_0$. A platform definition with the same convention exists on $\mathbb R^n$ (`StochasticProg.RecourseKKT.subdifferential`); this one-variable version avoids transporting $\kappa$ to `Fin 1 → ℝ`.
-- source:
--   Wang, Ran, Zhou, He, On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models, authors' manuscript (2025), Theorem 1, p.8; Appendix A, proof of Theorem 1, p.34

import Mathlib

open scoped ENNReal

namespace DRORSEquiv

/-- **The subdifferential `∂φ(τ)` of a function `φ : ℝ → [0, ∞]`** (used for `∂κ(τ)` in
Wang, Ran, Zhou, He, *On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models*, authors' manuscript (2025), Theorem 1, p.8, and Appendix A, p.34: "k∗(τ) ≥ k∗(τrs) + α(τ − τrs) for any τ ≥ Z0 by the
definition of subgradient"): `α ∈ ∂φ(τ)` when `φ(τ) < ∞` and `φ(τ') ≥ φ(τ) + α (τ' − τ)` for every
`τ' ∈ ℝ`.

**Formalization Note.** Convex-analysis convention: `∂φ(τ) = ∅` where `φ(τ) = ∞`, and points `τ'` with
`φ(τ') = ∞` impose no constraint. The paper's inequality ranges over `τ ≥ Z₀`; for `φ = κ` this is the
same set, because `κ = ∞` below `Z₀`. The inequality is read in `EReal`. -/
def subdiff (φ : ℝ → ℝ≥0∞) (τ : ℝ) : Set ℝ :=
  {α | φ τ < ⊤ ∧ ∀ τ' : ℝ, (φ τ : EReal) + ((α * (τ' - τ) : ℝ) : EReal) ≤ (φ τ' : EReal)}

end DRORSEquiv


