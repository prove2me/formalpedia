-- Prove2me | Definitions.Def_SimpleMenus_ClosingSide
-- name    : SimpleMenus_ClosingSide
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:35:59.1915+00:00
-- url     : https://prove2.me/theorems/f0e40b63-f083-46dd-8274-939509196d3e
-- title:
--   Common closing side at breakpoints (correction)
-- statement:
--   The family $\phi_1,\dots,\phi_K$ has a **common closing side** at the breakpoints $\mathcal B$ if at every $b\in\mathcal B$ either all $\phi_k$ are left-continuous at $b$, or all $\phi_k$ are right-continuous at $b$.
--
--   This condition is not in the paper. It is added to the constraint-reduction step of the proof of Theorem 1 and to Theorem 1, which are false without it. Counterexample: $K=2$, $\phi_1=\mathbb 1[w\le\omega]-1$, $\phi_2=\mathbb 1[w\ge\omega]-1$ (the paper's examples (IV) and (III)), one price level $v_1$ with $0<v_1<\omega<\bar v$. Then $\mathcal F=\{\delta_\omega\}$ and $\mathrm{CR}=v_1/\omega$, but every pair of left limits at the grid points is $(0,-1)$ or $(-1,0)$, so (4) has value $+\infty$. Every single-constraint example and every family of quantile constraints satisfies it.
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, correction to the proof of Theorem 1 (p.ec8) and Theorem 1 (p.11); counterexample in the mission description

import Mathlib

open Set

namespace SimpleMenus

/-- **Correction (common closing side).** At every breakpoint `b ∈ B`, either all `ϕ_k` are
left-continuous at `b`, or all `ϕ_k` are right-continuous at `b`.

This hypothesis is not in Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3. It is added to the constraint-reduction step of the proof of
Theorem 1 (p.ec8) and to Theorem 1, which are false without it. Counterexample (CE2): `K = 2`,
`ϕ₁ = 𝟙[w ≤ ω] − 1`, `ϕ₂ = 𝟙[w ≥ ω] − 1` (the paper's examples (IV) and (III)), `n = 1`,
`0 < v₁ < ω < v̄`, `x = 1`. Then `𝓕 = {δ_ω}` and `CR = v₁ / ω`, but every left limit pair at the grid
points is `(0, −1)` or `(−1, 0)`, so (4) has value `+∞`: at `ω` the sum `Σ_k λ_k ϕ_k` exceeds both
of its one-sided limits, which the reduction to left limits loses. -/
def ClosingSide {K : ℕ} (phi : Fin K → ℝ → ℝ) (B : Finset ℝ) : Prop :=
  ∀ b ∈ B, (∀ k, ContinuousWithinAt (phi k) (Iic b) b) ∨ (∀ k, ContinuousWithinAt (phi k) (Ici b) b)

end SimpleMenus


