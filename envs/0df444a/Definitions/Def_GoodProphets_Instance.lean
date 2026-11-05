-- Prove2me | Definitions.Def_GoodProphets_Instance
-- name    : GoodProphets_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:46.420091+00:00
-- url     : https://prove2.me/theorems/ab702250-7355-4831-8047-906ab385f15f
-- title:
--   Instance of the count-based objective: $A$, $D\ge0$ with a positive entry per row, $\vec B$, $\vec c_1$, $\vec c_2$
-- statement:
--   An **instance** of the objective of Banerjee and Freund with $k$ types, $\ell$ actions per type, $r$ constraint rows and $m$ penalty variables consists of
--
--   1. a constraint matrix $A\in\mathbb R^{r\times(k\ell)}$ whose columns are indexed by type-action pairs $(\theta,j)$;
--   2. a penalty matrix $D\in\mathbb R^{r\times m}$ that is **non-negative** and has **at least one positive entry in every row**;
--   3. a right-hand side $\vec B\in\mathbb R^r$;
--   4. cost vectors $\vec c_1\in\mathbb R^{k\ell}$ for the type-action counts and $\vec c_2\in\mathbb R^m$ for the penalty variables.
--
--   These data define the objective
--   $$
--   f_{\vec N}(\vec x)=\min_{\vec z}\ \vec c_1\cdot\vec x+\vec c_2\cdot\vec z\quad\text{s.t.}\quad \sum_j x_{\theta j}=N_\theta\ \forall\theta,\qquad A\vec x-D\vec z\le\vec B\sum_\theta N_\theta,\qquad \vec z\ge0 .
--   $$
--   Bin packing, online payment routing, network revenue management and egalitarian welfare are instances. The vector $\vec x$ models the decisions, $A\vec x\le \vec B\sum_\theta N_\theta$ the constraints, and $D\vec z$ relaxes those constraints at a penalty.
--
--   **Formalization Note** Types are `Fin k` and actions `Fin ℓ`. A type-action array is `x : Fin k → Fin ℓ → ℝ`, and `A i θ j` is the coefficient of $x_{\theta j}$ in row $i$.
-- source:
--   S. Banerjee and D. Freund, Good prophets know when the end is near, Management Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript, sha256 2cfd1ada…2c46), §2, p.7, "Objective Function"

import Mathlib

namespace GoodProphets

/-- An instance of the objective of Banerjee & Freund, *Good prophets know when the end is near*,
Management Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript), §2, p.7,
"Objective Function": the data `c⃗₁, c⃗₂, A, D, B⃗` of

`f_N(x) = min_z c⃗₁·x + c⃗₂·z  s.t.  ∑ⱼ x_θj = N_θ ∀θ,  A x − D z ≤ B⃗ ∑_θ N_θ,  z ≥ 0`,

where `D` is a non-negative matrix with at least one positive value in every row.

* `k` is the number of types `|Θ|`, `ℓ` the number of actions per type, `r` the number of rows of
  `A`, `D`, `B⃗`, and `m` the number of penalty variables `z`;
* `A i θ j` is the entry of `A` in row `i` and column `(θ, j)` (the coefficient of `x_θj`);
* `D i q` is the entry of `D` in row `i` and column `q`;
* `c1 θ j` is the cost of `x_θj` and `c2 q` the cost of `z_q`.

**Formalization Note** Types are `Fin k` and actions `Fin ℓ` (type `θ`'s action `a_θ(j+1)` is
`j`). The paper's `x⃗` is the array `x : Fin k → Fin ℓ → ℝ`. The two conditions on `D` are the
paper's (p.7); no other condition is imposed on the data. -/
structure Instance (k ℓ r m : ℕ) where
  /-- The constraint matrix `A`, row `i`, column `(θ, j)`. -/
  A : Fin r → Fin k → Fin ℓ → ℝ
  /-- The penalty matrix `D`. -/
  D : Fin r → Fin m → ℝ
  /-- The right-hand side `B⃗`, multiplied by `∑_θ N_θ` in the constraint. -/
  B : Fin r → ℝ
  /-- The cost vector `c⃗₁` of the type-action counts. -/
  c1 : Fin k → Fin ℓ → ℝ
  /-- The cost vector `c⃗₂` of the penalty variables. -/
  c2 : Fin m → ℝ
  /-- `D` is non-negative (p.7). -/
  D_nonneg : ∀ i q, 0 ≤ D i q
  /-- `D` has at least one positive value in every row (p.7). -/
  D_row_pos : ∀ i, ∃ q, 0 < D i q

end GoodProphets


