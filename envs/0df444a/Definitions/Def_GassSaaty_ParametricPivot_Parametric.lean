-- Prove2me | Definitions.Def_GassSaaty_ParametricPivot_Parametric
-- name    : GassSaaty_ParametricPivot_Parametric
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:22:32.820658+00:00
-- url     : https://prove2.me/theorems/685949b2-aeaa-464d-9d89-ead12050a8f7
-- title:
--   §2 Case A — the coefficients $\alpha_j,\beta_j$ of $z_j - c_j = \alpha_j + \lambda\beta_j$ and the critical values $\underline\lambda,\bar\lambda$ of (5)
-- statement:
--   Gass and Saaty study the linear program with a cost that depends linearly on a real parameter $\lambda$:
--
--   $$
--   \text{minimize } \sum_{j=1}^n (d_j + \lambda d'_j)\, x_j \quad \text{subject to } x_j \ge 0,\ \ \sum_{j=1}^n a_{ij} x_j = a_{i0}\ \ (i = 1,\dots,m).
--   $$
--
--   Fix a basis, that is, $m$ linearly independent columns $A_{B(1)},\dots,A_{B(m)}$ of the matrix $(a_{ij})$. Every column is written in this basis as $A_j = \sum_i y_{ij} A_{B(i)}$, and for a cost vector $c$ the simplex method sets $z_j = \sum_i y_{ij}\, c_{B(i)}$. For the parametric cost $c_j = d_j + \lambda d'_j$ the number $z_j - c_j$ is an affine function of $\lambda$, written
--
--   $$
--   z_j - c_j = \alpha_j + \lambda \beta_j ,
--   $$
--
--   so $\alpha_j$ is $z_j - c_j$ computed with the cost $d$ and $\beta_j$ is $z_j - c_j$ computed with the cost $d'$. The module defines:
--
--   1. $\alpha_j$ (`alpha A d B j`) and $\beta_j$ (`beta A d' B j`), for the basis $B$;
--   2. the upper critical value of (5), $\bar\lambda = \min_{\beta_j > 0} (-\alpha_j/\beta_j)$, equal to $+\infty$ when $\beta_j \le 0$ for every $j$;
--   3. the lower critical value of (5), $\underline\lambda = \max_{\beta_j < 0} (-\alpha_j/\beta_j)$, equal to $-\infty$ when $\beta_j \ge 0$ for every $j$.
--
--   The basis is optimal exactly for the $\lambda$ with $\alpha_j + \lambda\beta_j \le 0$ for all $j$ (inequalities (3)), and when (3) is consistent this is the interval $\underline\lambda \le \lambda \le \bar\lambda$ of (4). These are the quantities in which the paper states its THEOREM.
--
--   **Formalization Note** The linear program, bases, reduced costs and the coordinates $y_{ij}$ (`pivotColumn A B j i`) come from the published `LinearOptimization` definitions (Bertsimas–Tsitsiklis). Their reduced cost is $\bar c_j = c_j - c_B' B^{-1} A_j = -(z_j - c_j)$, so $\alpha_j$ and $\beta_j$ are defined as the **negatives** of the reduced costs for $d$ and $d'$; the paper's optimality condition $z_j - c_j \le 0$ is the platform's $\bar c_j \ge 0$. $\bar\lambda$ is valued in `WithTop ℝ` (a finite infimum, $\top = +\infty$ for the empty index set) and $\underline\lambda$ in `WithBot ℝ` ($\bot = -\infty$); no real-valued infimum of a possibly empty set is used. The indices $j$ are 0-based (`Fin n`). The definitions are meant for a genuine basis (`IsStdBasis A B`); every theorem using them assumes it.
-- source:
--   Gass and Saaty, The computational algorithm for the parametric objective function, Naval Res. Logist. Quart. 2 (1955), p. 39, Eqs. (1)–(2); p. 40, Section 2, Case A, footnote 4 and Eqs. (3)–(5)

import Mathlib
import Definitions.Def_LinearOptimization_SimplexPivot

open Matrix

namespace GassSaaty.ParametricPivot

open LinearOptimization

/-- Gass–Saaty §2, Case A (p. 40) and footnote 4: the coefficient `α_j` of the linear function
`"z_j − c_j" = α_j + λβ_j` with respect to the basis `B`, i.e. `z_j − c_j` computed for the cost
vector `d`. Here `z_j = Σ_i y_ij c_{B(i)}` with `y_ij = (B⁻¹A_j)_i`, so `z_j − c_j` is the
**negative** of the Bertsimas–Tsitsiklis reduced cost `reducedCost A d B j = d_j − d_B'B⁻¹A_j`. -/
noncomputable def alpha {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ)
    (B : Fin m ↪ Fin n) (j : Fin n) : ℝ :=
  -reducedCost A d B j

/-- Gass–Saaty §2, Case A (p. 40): the coefficient `β_j` of `λ` in `"z_j − c_j" = α_j + λβ_j`
with respect to the basis `B`, i.e. `z_j − c_j` computed for the cost vector `d'`
(negative of the reduced cost `reducedCost A d' B j`). -/
noncomputable def beta {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (d' : Fin n → ℝ)
    (B : Fin m ↪ Fin n) (j : Fin n) : ℝ :=
  -reducedCost A d' B j

/-- Gass–Saaty Eq. (5), right half (p. 40): `λ̄ = min_{β_j > 0} (−α_j/β_j)`, and `λ̄ = +∞` if
`β_j ≤ 0` for every `j`. Valued in `WithTop ℝ`: the infimum of the empty family is `⊤ = +∞`. -/
noncomputable def lamBar {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (d d' : Fin n → ℝ)
    (B : Fin m ↪ Fin n) : WithTop ℝ :=
  (Finset.univ.filter fun j => 0 < beta A d' B j).inf
    fun j => ((-alpha A d B j / beta A d' B j : ℝ) : WithTop ℝ)

/-- Gass–Saaty Eq. (5), left half (p. 40): `λ̲ = max_{β_j < 0} (−α_j/β_j)`, and `λ̲ = −∞` if
`β_j ≥ 0` for every `j`. Valued in `WithBot ℝ`: the supremum of the empty family is `⊥ = −∞`. -/
noncomputable def lamLower {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (d d' : Fin n → ℝ)
    (B : Fin m ↪ Fin n) : WithBot ℝ :=
  (Finset.univ.filter fun j => beta A d' B j < 0).sup
    fun j => ((-alpha A d B j / beta A d' B j : ℝ) : WithBot ℝ)

end GassSaaty.ParametricPivot


