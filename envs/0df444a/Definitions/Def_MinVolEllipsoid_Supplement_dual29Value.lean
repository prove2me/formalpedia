-- Prove2me | Definitions.Def_MinVolEllipsoid_Supplement_dual29Value
-- name    : MinVolEllipsoid_Supplement_dual29Value
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:31:53.801736+00:00
-- url     : https://prove2.me/theorems/6d293d54-0c17-4e55-a362-58da0c7ae66b
-- title:
--   Optimal value of the Lagrange dual (29)
-- statement:
--   For $S\in\mathbb R^{J\times K}$ and $t\in\mathbb R^J$, the Lagrange dual (29) of problem (28) is
--
--   $$
--   \begin{aligned}
--   \inf\quad & K\rho^\top t-K-\log\det\Bigl(-\tfrac12\bigl(S^\top\Lambda+\Lambda^\top S\bigr)\Bigr)\\
--   \text{s.t.}\quad & \Lambda\in\mathbb R^{J\times K},\ \rho\in\mathbb R^J,\\
--   & S^\top\rho=0,\\
--   & \|\Lambda_{j:}\|\le\rho_j\quad\forall j\in[J],
--   \end{aligned}
--   $$
--
--   where $\Lambda_{j:}\in\mathbb R^K$ is the transpose of the $j$-th row of $\Lambda$ and $\|\cdot\|$ the Euclidean norm. This definition is its optimal value, an extended real number, with $(\Lambda,\rho)$ ranging over the points where $-\tfrac12(S^\top\Lambda+\Lambda^\top S)$ is positive definite (the domain of $\log\det$). The same problem appears as (14) in the proof of Theorem 3.
--
--   **Formalization Note** $K$ is the dimension $n$ as a real number; $\rho^\top t$ is a dot product; $\|v\|=\sqrt{v^\top v}$. The value lives in `EReal` ($+\infty$ if infeasible).
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, Appendix B.1, display (29), p.31; display (14), p.12

import Mathlib

open Matrix

namespace MinVolEllipsoid.Supplement

/-- **The optimal value of the Lagrange dual (29)** (Mittal & Hanasusanto, arXiv:1807.07507v4,
Appendix B.1, display (29), p.31; the same problem is (14), p.12).

`dual29Value S t` is

`inf { Kρ⊤t − K − log det(−½(S⊤Λ + Λ⊤S)) : Λ ∈ ℝ^{J×K}, ρ ∈ ℝᴶ, S⊤ρ = 0, ‖Λ_{j:}‖ ≤ ρ_j ∀ j ∈ [J] }`,

the infimum taken over the `(Λ, ρ)` for which `−½(S⊤Λ + Λ⊤S)` is positive definite (the domain of
`log det`). `Λ_{j:} ∈ ℝᴷ` is the transpose of the `j`-th row of `Λ` and `‖·‖` the Euclidean norm.

**Formalization Note** `K` is the dimension `n`, used as `(n : ℝ)`; `ρ⊤t` is `ρ ⬝ᵥ t`;
`Λ_{j:}` is the row `Λ j`, and `‖v‖` is `√(v ⬝ᵥ v)`. The value is in `EReal` (`⊤` if infeasible). -/
noncomputable def dual29Value {n m : ℕ} (S : Matrix (Fin m) (Fin n) ℝ) (t : Fin m → ℝ) : EReal :=
  ⨅ (Λ : Matrix (Fin m) (Fin n) ℝ) (ρ : Fin m → ℝ)
    (_ : Sᵀ *ᵥ ρ = 0 ∧ (∀ j, Real.sqrt (Λ j ⬝ᵥ Λ j) ≤ ρ j) ∧
      (-((1 / 2 : ℝ) • (Sᵀ * Λ + Λᵀ * S))).PosDef),
    (((n : ℝ) * (ρ ⬝ᵥ t) - (n : ℝ) - Real.log (-((1 / 2 : ℝ) • (Sᵀ * Λ + Λᵀ * S))).det : ℝ) : EReal)

end MinVolEllipsoid.Supplement


