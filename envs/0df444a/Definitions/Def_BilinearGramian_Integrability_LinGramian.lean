-- Prove2me | Definitions.Def_BilinearGramian_Integrability_LinGramian
-- name    : BilinearGramian_Integrability_LinGramian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:38:21.334515+00:00
-- url     : https://prove2.me/theorems/75fee58b-fa53-4299-be29-c43c9c02f628
-- title:
--   The Lyapunov equation (3.9) for the Gramian P̃(x) of the linearization, and controllable pairs
-- statement:
--   Fix integers $n, m \ge 0$ and real matrices $A \in \mathbb R^{n\times n}$, $N_1,\dots,N_m \in \mathbb R^{n\times n}$ and $B \in \mathbb R^{n\times m}$, the data of the bilinear control system
--   $$\dot x = Ax + \sum_{j=1}^m N_j x\,u_j + Bu .$$
--   Write $b_j$ for the $j$-th column of $B$. For a point $x \in \mathbb R^n$, a matrix $\tilde P \in \mathbb R^{n\times n}$ **solves (3.9) at $x$** if
--   $$A \tilde P + \tilde P A^T = -\sum_{j=1}^m (N_j x + b_j)(N_j x + b_j)^T .$$
--   Its solution $\tilde P(x)$ is the controllability Gramian of the linearization of the system at the state $x$ and the input $u = 0$; when $A$ is stable, (3.9) has exactly one solution for each $x$.
--
--   The file also fixes the standard notion of a **controllable pair**: $(A, B)$ is controllable if the Kalman matrix $[B, AB, \dots, A^{n-1}B]$ has rank $n$, i.e. the only vector $v$ with $v^T A^k B = 0$ for all $k = 0, \dots, n-1$ is $v = 0$. The paper calls the bilinear system **locally controllable** if $(A, B)$ is controllable.
--
--   These are the two notions Example 3.3 of the paper is phrased in: the field $x \mapsto \tilde P(x)^{-1}x$ is built from (3.9), and the example system is required to be locally controllable.
--
--   **Formalization Note** The paper's indices $j = 1,\dots,m$ are `Fin m`; `gramRHS N B x` is the sum $\sum_j (N_j x + b_j)(N_j x + b_j)^T$ (without the minus sign), and `IsLinGramian A N B x P` is the equation (3.9) for the matrix `P`. Rank $n$ of the Kalman matrix is stated as triviality of its left kernel, which is equivalent.
-- source:
--   Benner, Damm, Lyapunov Equations, Energy Functionals, and Model Order Reduction of Bilinear and Stochastic Systems, SIAM J. Control Optim. 49(2) (2011), p. 697, eq. (3.9); p. 694 (local controllability)

import Mathlib

open Matrix

namespace BilinearGramian.Integrability

/-- The right-hand side of (3.9) of Benner–Damm (SIAM J. Control Optim. 49(2) (2011), p. 697),
without its minus sign: `∑_{j=1}^m (N_j x + b_j)(N_j x + b_j)ᵀ`, where `b_j` is the `j`-th column
of `B`. The paper's indices `j = 1, …, m` are `Fin m`. -/
def gramRHS {n m : ℕ} (N : Fin m → Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ j, vecMulVec (N j *ᵥ x + fun i => B i j) (N j *ᵥ x + fun i => B i j)

/-- `P` solves the Lyapunov equation (3.9) at the point `x`:
`A P + P Aᵀ = -∑_{j=1}^m (N_j x + b_j)(N_j x + b_j)ᵀ`. The solution `P̃(x)` is the
controllability Gramian of the linearization of (3.1) at `x` and `u = 0`. -/
def IsLinGramian {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (N : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (x : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A * P + P * Aᵀ = -gramRHS N B x

/-- The pair `(A, B)` is controllable (Kalman rank condition): the matrix
with the blocks `A^k B`, `k < n`, has rank `n`, stated as "its left kernel is trivial": the only `v` with
`vᵀ A^k B = 0` for all `k < n` is `v = 0`. -/
def IsControllable {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) :
    Prop :=
  ∀ v : Fin n → ℝ, (∀ k < n, v ᵥ* (A ^ k * B) = 0) → v = 0

end BilinearGramian.Integrability


