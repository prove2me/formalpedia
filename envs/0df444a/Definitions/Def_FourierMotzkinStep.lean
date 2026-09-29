-- Prove2me | Definitions.Def_FourierMotzkinStep
-- name    : FourierMotzkinStep
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-05T01:18:16.098294+00:00
-- url     : https://prove2.me/theorems/195393a6-58a0-420a-9ad6-91d2a5ff806b
-- title:
--   Fourier–Motzkin elimination step
-- statement:
--   **(Elimination algorithm, §2.8, pp. 71-72)** We are given a polyhedron $P$ in terms of linear inequality constraints
--
--   $$\sum_{j=1}^n a_{ij}x_j \ge b_i, \quad i = 1, \dots, m,$$
--
--   and wish to eliminate $x_n$.
--
--   **Step 1:** rewrite each constraint in the form
--
--   $$a_{in}x_n \ge -\sum_{j=1}^{n-1} a_{ij}x_j + b_i;$$
--
--   if $a_{in} \ne 0$, divide both sides by $a_{in}$. Letting $\bar{x} = (x_1, \dots, x_{n-1})$, we obtain an equivalent representation of $P$ involving the constraints
--
--   - $x_n \ge d_i + \mathbf{f}_i'\bar{x}$ (if $a_{in} > 0$),
--   - $d_j + \mathbf{f}_j'\bar{x} \ge x_n$ (if $a_{jn} < 0$), and
--   - $0 \ge d_k + \mathbf{f}_k'\bar{x}$ (if $a_{kn} = 0$),
--
--   where each $d_i, d_j, d_k$ is a scalar and each $\mathbf{f}_i, \mathbf{f}_j, \mathbf{f}_k$ is a vector in $\mathbb{R}^{n-1}$.
--
--   **Step 2:** let $Q$ be the polyhedron in $\mathbb{R}^{n-1}$ defined by the constraints
--
--   - $d_j + \mathbf{f}_j'\bar{x} \ge d_i + \mathbf{f}_i'\bar{x}$ (if $a_{in} > 0$ and $a_{jn} < 0$) and
--   - $0 \ge d_k + \mathbf{f}_k'\bar{x}$ (if $a_{kn} = 0$).
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, §2.8, Elimination algorithm, pp. 71-72

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Definitions.Def_Polyhedron

/-!
Fourier–Motzkin elimination (one step).

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997, §2.8, "Elimination algorithm" (boxed, p. 72):
given `P = {x ∈ ℝⁿ | Σⱼ aᵢⱼxⱼ ≥ bᵢ, i = 1, …, m}`, rewrite each constraint
as `aᵢₙxₙ ≥ −Σ_{j<n} aᵢⱼxⱼ + bᵢ` and, if `aᵢₙ ≠ 0`, divide by `aᵢₙ`,
obtaining `xₙ ≥ dᵢ + fᵢ'x̄` (if `aᵢₙ > 0`), `dⱼ + fⱼ'x̄ ≥ xₙ` (if
`aⱼₙ < 0`), `0 ≥ d_k + f_k'x̄` (if `a_kn = 0`), where `x̄ = (x₁, …, x_{n−1})`.
Then `Q ⊆ ℝⁿ⁻¹` is defined by the constraints
`dⱼ + fⱼ'x̄ ≥ dᵢ + fᵢ'x̄` (for `aᵢₙ > 0` and `aⱼₙ < 0`) and
`0 ≥ d_k + f_k'x̄` (for `a_kn = 0`).

Theorem 2.10 (p. 73) then states `Q = Π_{n−1}(P)`.
-/

open Matrix Finset

namespace LinearOptimization

/-- The scalar `dᵢ + fᵢ'x̄ = (bᵢ − Σ_{j<n} aᵢⱼx̄ⱼ)/aᵢₙ` obtained by solving
constraint `i` for `xₙ` (Bertsimas & Tsitsiklis, p. 72, Eqs. (2.4)–(2.5)); meaningful when
`aᵢₙ ≠ 0`. -/
noncomputable def fourierMotzkinBound {m n : ℕ}
    (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (b : Fin m → ℝ) (i : Fin m)
    (y : Fin n → ℝ) : ℝ :=
  (b i - ∑ l : Fin n, A i l.castSucc * y l) / A i (Fin.last n)

/-- **Bertsimas & Tsitsiklis, Elimination algorithm, step 2 (p. 72).** The polyhedron
`Q ⊆ ℝⁿ⁻¹` produced by eliminating `xₙ` from `{x | Ax ≥ b}`: the
lower bound from every positive row must not exceed the upper bound from
every negative row, and the rows not involving `xₙ` are kept. -/
noncomputable def fourierMotzkinEliminate {m n : ℕ}
    (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (b : Fin m → ℝ) :
    Set (Fin n → ℝ) :=
  {y | (∀ k, A k (Fin.last n) = 0 → b k ≤ ∑ l : Fin n, A k l.castSucc * y l) ∧
    ∀ i j, 0 < A i (Fin.last n) → A j (Fin.last n) < 0 →
      fourierMotzkinBound A b i y ≤ fourierMotzkinBound A b j y}

end LinearOptimization


