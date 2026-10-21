-- Prove2me | Definitions.Def_YeIPA_WorstCase_RankOneUpdate
-- name    : YeIPA_WorstCase_RankOneUpdate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:56:52.258649+00:00
-- url     : https://prove2.me/theorems/33265458-98f8-4012-b1e0-2b45efacda0f
-- title:
--   The rank-one updating scaling $D^t$ and the update sets $I^t$ of §5.1
-- statement:
--   Let $x^0,x^1,x^2,\dots\in\mathbb R^n$ be positive vectors (the iterates of an interior-point algorithm). Section 5.1 of Ye's *Interior Point Algorithms* replaces the scaling $X^t=\operatorname{diag}(x^t)$ of the normal matrix by a diagonal matrix $D^t=\operatorname{diag}(d^t)$ that changes only in the coordinates where $x^t$ has moved by more than a factor $1.1$:
--   $$d^0=x^0,\qquad d^t_j=\begin{cases}d^{t-1}_j & \text{if } 1/1.1\le d^{t-1}_j/x^t_j\le 1.1,\\ x^t_j & \text{otherwise},\end{cases}\qquad t\ge1.$$
--   The **update set** at iteration $t\ge1$ is
--   $$I^t=\{i: d^{t-1}_i/x^t_i\notin[1/1.1,\,1.1]\},$$
--   the coordinates reset to the current iterate (each costs one rank-one update of the inverse normal matrix). The module also defines the Euclidean norm $\|v\|=(\sum_jv_j^2)^{1/2}$ and the max-norm $\|v\|_\infty=\max_j|v_j|$.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ`; $d^t$ is `scaling x t`, defined by recursion on $t$, and $I^t$ is the finset `updateSet x t`, used only for $t\ge1$ (at $t=0$ the natural-number subtraction gives $d^0/x^0=1$ and an empty set). The book prints $I^t=\{i: d^t_i/x^t_i\notin[1/1.1,1.1]\}$, with $d^t$ in the numerator; read literally that set is always empty, since $d^t_i/x^t_i$ lies in $[1/1.1,1.1]$ by construction. The proof of Lemma 5.1 uses $I^t$ as the set of coordinates with $d^t_i=x^t_i\neq d^{t-1}_i$, i.e. with $d^{t-1}$ in the numerator, and that is what is defined here. The Euclidean norm is written out as `norm2` because Mathlib's norm on `Fin n → ℝ` is the sup norm.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 148, Section 5.1 (D^t, I^t)

import Mathlib

namespace YeIPA.WorstCase

/-!
# The rank-one updating rule of Chapter 5, §5.1

Ye, *Interior Point Algorithms: Theory and Analysis*, Wiley 1997, p. 148: given iterates
`x⁰, x¹, … > 0`, the diagonal scaling `Dᵗ = diag(dᵗ)` is `D⁰ = X⁰` and, for `t ≥ 1`,
`d_jᵗ = d_jᵗ⁻¹` if `1/1.1 ≤ d_jᵗ⁻¹ / x_jᵗ ≤ 1.1`, and `d_jᵗ = x_jᵗ` otherwise; `Iᵗ` is the set
of indices updated at iteration `t`. The book's indices `1, …, n` are `0, …, n-1` here.
-/

variable {n : ℕ}

/-- The Euclidean norm `‖v‖ = (∑ⱼ vⱼ²)^{1/2}`. -/
noncomputable def norm2 (v : Fin n → ℝ) : ℝ := Real.sqrt (∑ j, v j ^ 2)

/-- The max-norm `‖v‖_∞ = maxⱼ |vⱼ|` (equal to `0` when `n = 0`). -/
noncomputable def normInf (v : Fin n → ℝ) : ℝ := ⨆ j, |v j|

/-- The diagonal of `Dᵗ` (p. 148): `d⁰ = x⁰` and, for `t ≥ 0`,
`d_j^{t+1} = d_jᵗ` if `1/1.1 ≤ d_jᵗ / x_j^{t+1} ≤ 1.1`, else `d_j^{t+1} = x_j^{t+1}`. -/
noncomputable def scaling (x : ℕ → Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => x 0
  | t + 1 => fun j =>
      if 1 / 1.1 ≤ scaling x t j / x (t + 1) j ∧ scaling x t j / x (t + 1) j ≤ 1.1 then
        scaling x t j
      else x (t + 1) j

/-- The update set `Iᵗ = {i : d_iᵗ⁻¹ / x_iᵗ ∉ [1/1.1, 1.1]}` for `t ≥ 1` (p. 148): the indices
whose scaling is reset to the current iterate at iteration `t`. (The book prints `d_iᵗ` in the
numerator, under which `Iᵗ` would always be empty; its proof of Lemma 5.1 uses `d_iᵗ⁻¹`.)
Only used for `t ≥ 1`. -/
noncomputable def updateSet (x : ℕ → Fin n → ℝ) (t : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i =>
    ¬ (1 / 1.1 ≤ scaling x (t - 1) i / x t i ∧ scaling x (t - 1) i / x t i ≤ 1.1)

end YeIPA.WorstCase


