-- Prove2me | Definitions.Def_BiasVarianceMinimax_xi
-- name    : BiasVarianceMinimax_xi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:30:43.973366+00:00
-- url     : https://prove2.me/theorems/30a135e7-8db3-4044-94fb-59c9e2422ae9
-- title:
--   The function $\phi$ and the matrix $\Xi$
-- statement:
--   Let $\phi(\kappa)=\sum_{j=1}^n (j+n_0)^{-\kappa}$, and write $\kappa_1=\frac{q_1+2q_2}{2(q_1+q_2)}$, $\kappa_2=\frac{q_2}{q_1+q_2}$. The matrix
--
--   $$\Xi=\begin{bmatrix}\xi_{11}&\xi_{12}\\ \xi_{21}&\xi_{22}\end{bmatrix}=\begin{bmatrix}\phi(1)&\phi(\kappa_1)\\ \phi(\kappa_1)&\phi(\kappa_2)\end{bmatrix}^{-1}$$
--
--   depends on the budget $n$ and carries all the dependence of the optimal weights on $n$.
--
--   **Formalization Note** The inverse is `Matrix`'s, which returns $0$ on a singular matrix; this happens for $n\le 1$, and for $n\ge 2$ the determinant is positive. Lean's indices are zero-based, so `xi … 0 0` is $\xi_{11}$.
-- source:
--   Lam, Zhang & Zhang, arXiv:1902.04673v1, Theorem 8, p.21; (73), p.54

import Mathlib
import Definitions.Def_BiasVarianceMinimax_deltaGrid

namespace BiasVarianceMinimax

/-- `φ(κ) = ∑_{j=1}^n 1/(j + n₀)^κ`. Lam, Zhang & Zhang, arXiv:1902.04673v1, Theorem 8, p.21. -/
noncomputable def phi (n₀ n : ℕ) (κ : ℝ) : ℝ :=
  ∑ i : Fin n, 1 / runPoint n₀ i ^ κ

/-- The faster decay rate `κ₁ = (q₁ + 2 q₂)/(2(q₁ + q₂))`. Lam, Zhang & Zhang,
arXiv:1902.04673v1, Theorem 8, p.20. -/
noncomputable def kappaOne (q₁ q₂ : ℝ) : ℝ := (q₁ + 2 * q₂) / (2 * (q₁ + q₂))

/-- The slower decay rate `κ₂ = q₂/(q₁ + q₂)`. Lam, Zhang & Zhang, arXiv:1902.04673v1,
Theorem 8, p.20. -/
noncomputable def kappaTwo (q₁ q₂ : ℝ) : ℝ := q₂ / (q₁ + q₂)

/-- The matrix `Ξ = (ξᵢⱼ)` at budget `n`, the inverse of `[φ(1), φ(κ₁); φ(κ₁), φ(κ₂)]`.
Lam, Zhang & Zhang, arXiv:1902.04673v1, Theorem 8, p.21; (73), p.54.

**Formalization Note.** `⁻¹` is `Matrix`'s inverse, which returns `0` on a singular matrix. That
happens at `n ≤ 1`; for `n ≥ 2` the determinant is positive (proved in the verification file).
Entries are zero-based: `xi … 0 0` is `ξ₁₁`, `xi … 0 1` is `ξ₁₂`, `xi … 1 1` is `ξ₂₂`. -/
noncomputable def xi (q₁ q₂ : ℝ) (n₀ n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (!![phi n₀ n 1, phi n₀ n (kappaOne q₁ q₂);
      phi n₀ n (kappaOne q₁ q₂), phi n₀ n (kappaTwo q₁ q₂)])⁻¹

end BiasVarianceMinimax


