-- Prove2me | Definitions.Def_RobustLS_Tikhonov_Core
-- name    : RobustLS_Tikhonov_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:27:52.412339+00:00
-- url     : https://prove2.me/theorems/17f839e1-db88-44fb-b42e-59f595d77189
-- title:
--   The SOCP (15), its dual, and minimum-norm solutions of $Ax = b$
-- statement:
--   Fix a matrix $A \in \mathbb R^{n\times m}$ and a vector $b \in \mathbb R^n$. All vector norms are Euclidean, $\|v\| = \sqrt{\sum_i v_i^2}$.
--
--   1. **The SOCP (15).** A triple $(x, \lambda, \tau) \in \mathbb R^m \times \mathbb R \times \mathbb R$ is *feasible* for the second-order cone program
--   $$\text{minimize } \lambda \quad\text{subject to}\quad \|Ax - b\| \le \lambda - \tau,\qquad \left\|\begin{bmatrix} x \\ 1\end{bmatrix}\right\| \le \tau$$
--   if it satisfies both cone constraints; here $\left\|\begin{bmatrix} x \\ 1\end{bmatrix}\right\| = \sqrt{\|x\|^2 + 1}$ is the norm of the vector $x$ with a coordinate $1$ appended. A feasible triple is *optimal* if its objective $\lambda$ is at most the objective $\lambda'$ of every feasible triple $(x', \lambda', \tau')$.
--   2. **The dual of (15).** A triple $(z, u, v) \in \mathbb R^n \times \mathbb R^m \times \mathbb R$ is *dual feasible* if
--   $$A^\top z + u = 0,\qquad \|z\| \le 1,\qquad \left\|\begin{bmatrix} u \\ v\end{bmatrix}\right\| \le 1,$$
--   its *dual objective* is $b^\top z - v$, and it is *dual optimal* if it is dual feasible and its objective is at least that of every dual feasible triple.
--   3. **Minimum-norm solutions.** A vector $x \in \mathbb R^m$ is a *minimum-norm solution* of $Ax = b$ if $Ax = b$ and $\|x\| \le \|y\|$ for every $y$ with $Ay = b$. When the system is consistent this vector is unique and equals $A^\dagger b$, where $A^\dagger$ is the Moore–Penrose pseudoinverse.
--
--   Program (15) computes the robust least-squares (RLS) solution of El Ghaoui and Lebret for unit perturbation level $\rho = 1$, and its dual is the program they derive from the general second-order cone duality of their §2.1; these objects are what Theorem 3.2 and its proof are stated in terms of.
--
--   **Formalization Note** Vectors are functions `Fin k → ℝ` and `eucNorm` is the Euclidean norm written out (`‖·‖` on `Fin k → ℝ` in Mathlib is the sup norm). The stacked vectors $[x;1]$ and $[u;v]$ are indexed by `Fin m ⊕ Unit`. Mathlib has no Moore–Penrose pseudoinverse for matrices, so $A^\dagger b$ enters through the minimum-norm characterization, which is the form the paper's proof uses.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), DOI 10.1137/S0895479896298130, p. 1040 (PDF p. 6), Theorem 3.1, Eq. (15), and proof of Theorem 3.2 (dual of (15)); p. 1041 (PDF p. 7), proof of Theorem 3.2 (minimum-norm solution, x = A†b); Notation, p. 1035 (PDF p. 1)

import Mathlib

namespace RobustLS.Tikhonov

open Matrix

/-- The Euclidean norm `‖v‖ = √(∑ᵢ vᵢ²)` of a real vector indexed by a finite type.
El Ghaoui & Lebret, *Robust Solutions to Least-Squares Problems with Uncertain Data*,
SIAM J. Matrix Anal. Appl. 18(4) (1997), Notation, p. 1035 (PDF p. 1): vectors carry the
Euclidean norm. (Stated explicitly because `‖v‖` on `ι → ℝ` in Mathlib is the sup norm.) -/
noncomputable def eucNorm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The stacked vector `[x; 1] ∈ ℝ^{m+1}`: the coordinates of `x` (indexed by `Fin m`) followed
by the single coordinate `1` (indexed by `Unit`). El Ghaoui & Lebret (1997), (15), p. 1040
(PDF p. 6). Its Euclidean norm is `√(‖x‖² + 1)`. -/
def stackOne {m : ℕ} (x : Fin m → ℝ) : Fin m ⊕ Unit → ℝ :=
  Sum.elim x (fun _ => 1)

/-- The stacked vector `[u; v] ∈ ℝ^{m+1}` of a vector `u ∈ ℝ^m` and a scalar `v`.
El Ghaoui & Lebret (1997), dual of (15), p. 1040 (PDF p. 6). -/
def stackScalar {m : ℕ} (u : Fin m → ℝ) (v : ℝ) : Fin m ⊕ Unit → ℝ :=
  Sum.elim u (fun _ => v)

/-- Feasibility for the second-order cone program (15) of El Ghaoui & Lebret (1997),
Theorem 3.1, p. 1040 (PDF p. 6):
`minimize λ subject to ‖Ax − b‖ ≤ λ − τ, ‖[x; 1]‖ ≤ τ`,
in the variables `x ∈ ℝ^m`, `λ, τ ∈ ℝ` (all norms Euclidean). -/
def IsSOCPFeasible {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) (lam tau : ℝ) : Prop :=
  eucNorm (A *ᵥ x - b) ≤ lam - tau ∧ eucNorm (stackOne x) ≤ tau

/-- Optimality for the SOCP (15) (El Ghaoui & Lebret 1997, p. 1040, PDF p. 6): `(x, λ, τ)` is
feasible and its objective `λ` is at most the objective `λ'` of every feasible `(x', λ', τ')`. -/
def IsSOCPOptimal {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) (lam tau : ℝ) : Prop :=
  IsSOCPFeasible A b x lam tau ∧
    ∀ (x' : Fin m → ℝ) (lam' tau' : ℝ), IsSOCPFeasible A b x' lam' tau' → lam ≤ lam'

/-- Feasibility for the problem dual to (15), El Ghaoui & Lebret (1997), proof of Theorem 3.2,
p. 1040 (PDF p. 6):
`maximize bᵀz − v subject to Aᵀz + u = 0, ‖z‖ ≤ 1, ‖[u; v]‖ ≤ 1`,
in the variables `z ∈ ℝ^n`, `u ∈ ℝ^m`, `v ∈ ℝ` (Euclidean norms). -/
def IsDualFeasible {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (z : Fin n → ℝ) (u : Fin m → ℝ) (v : ℝ) : Prop :=
  Aᵀ *ᵥ z + u = 0 ∧ eucNorm z ≤ 1 ∧ eucNorm (stackScalar u v) ≤ 1

/-- The objective `bᵀz − v` of the problem dual to (15) (El Ghaoui & Lebret 1997, p. 1040). -/
def dualObjective {n : ℕ} (b : Fin n → ℝ) (z : Fin n → ℝ) (v : ℝ) : ℝ :=
  b ⬝ᵥ z - v

/-- Optimality for the problem dual to (15) (El Ghaoui & Lebret 1997, p. 1040, PDF p. 6):
`(z, u, v)` is dual feasible and its objective `bᵀz − v` is at least that of every dual feasible
point. -/
def IsDualOptimal {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (z : Fin n → ℝ) (u : Fin m → ℝ) (v : ℝ) : Prop :=
  IsDualFeasible A z u v ∧
    ∀ (z' : Fin n → ℝ) (u' : Fin m → ℝ) (v' : ℝ), IsDualFeasible A z' u' v' →
      dualObjective b z' v' ≤ dualObjective b z v

/-- `x` is a minimum-norm solution of `Ax = b`: it solves `Ax = b`, and its Euclidean norm is at
most that of every other solution. This is how `A†b` (the Moore–Penrose pseudoinverse of `A`
applied to `b`, Notation, p. 1035) enters El Ghaoui & Lebret (1997), proof of Theorem 3.2,
p. 1041 (PDF p. 7): "the optimal x is the (unique) minimum-norm solution to Ax = b: x = A†b".
(When `Ax = b` is consistent, `A†b` is exactly the unique minimum-norm solution.) -/
def IsMinNormSolution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) : Prop :=
  A *ᵥ x = b ∧ ∀ y : Fin m → ℝ, A *ᵥ y = b → eucNorm x ≤ eucNorm y

end RobustLS.Tikhonov


