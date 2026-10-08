-- Prove2me | Definitions.Def_BilinearGramian_Kernel_GramianEquations
-- name    : BilinearGramian_Kernel_GramianEquations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:38:43.812932+00:00
-- url     : https://prove2.me/theorems/b611b11b-7e60-4a24-af79-f06a97d42fcc
-- title:
--   The generalized Lyapunov equations (3.6) for the Gramians $P$ and $Q$
-- statement:
--   For $A, N_1,\dots,N_m\in\mathbb R^{n\times n}$, $B\in\mathbb R^{n\times m}$ and $C\in\mathbb R^{p\times n}$, the **generalized Lyapunov equations** (3.6) of the bilinear system (3.1)–(3.2) are
--   $$AP + PA^T + \sum_{j=1}^m N_j P N_j^T = -BB^T, \qquad A^TQ + QA + \sum_{j=1}^m N_j^T Q N_j = -C^TC,$$
--   for unknown matrices $P, Q \in \mathbb R^{n\times n}$. A solution $P$ of the first equation is the (algebraic) **controllability Gramian** and a solution $Q$ of the second the **observability Gramian** of the bilinear system. This file defines the two predicates "$P$ solves the first equation" and "$Q$ solves the second equation".
--
--   Nothing is assumed about existence or uniqueness of solutions, or about stability of $A$: the statements of the mission take any solution, and add nonnegative definiteness ($P \ge 0$, $Q\ge 0$) as a separate hypothesis exactly where the paper does.
--
--   **Formalization Note** Nonnegative definiteness is Mathlib's `Matrix.PosSemidef`, which includes symmetry; it is not part of these predicates.
-- source:
--   Benner, Damm, Lyapunov Equations, Energy Functionals, and Model Order Reduction of Bilinear and Stochastic Systems, SIAM J. Control Optim. 49(2) (2011), p. 695, eq. (3.6)

import Mathlib

open Matrix

namespace BilinearGramian.Kernel

/-- The first generalized Lyapunov equation of (3.6) (Benner–Damm 2011, p. 695), whose solution
`P` is the controllability (reachability) Gramian of the bilinear system (3.1):
`A P + P Aᵀ + ∑_{j=1}^m N_j P N_jᵀ = -B Bᵀ`. -/
def ReachGramianEq {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin m → Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A * P + P * Aᵀ + ∑ j, N j * P * (N j)ᵀ = -(B * Bᵀ)

/-- The second generalized Lyapunov equation of (3.6) (Benner–Damm 2011, p. 695), whose solution
`Q` is the observability Gramian of the bilinear system (3.1)–(3.2):
`Aᵀ Q + Q A + ∑_{j=1}^m N_jᵀ Q N_j = -Cᵀ C`. -/
def ObsGramianEq {n m p : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin p) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Aᵀ * Q + Q * A + ∑ j, (N j)ᵀ * Q * N j = -(Cᵀ * C)

end BilinearGramian.Kernel


