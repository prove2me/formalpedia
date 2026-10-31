-- Prove2me | Definitions.Def_QKPSDP_IsGlobalOptSQKE
-- name    : QKPSDP_IsGlobalOptSQKE
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:49:20.307812+00:00
-- url     : https://prove2.me/theorems/ca6db718-34ae-4599-b7d4-4f90204452c6
-- title:
--   Global optimal solutions of (SQKE)
-- statement:
--   Let $C \in \mathbb S^n$. A pair $(x, X)$, equivalently $Y = \begin{pmatrix} 1 & x^\top \\ x & X\end{pmatrix}$, is a **global optimal solution** of (SQKE) if it is feasible and
--
--   $$
--   -\langle C, X\rangle \le -\langle C, X'\rangle \quad\text{for every feasible } (x', X'),
--   $$
--
--   with $\langle A, B\rangle = \operatorname{Tr}(AB^\top)$.
--
--   This is optimality for the convex SDP, over feasible points of every rank.
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, (SQKE), p.2; ⟨A, B⟩ := Tr(AB⊤), p.4

import Mathlib
import Definitions.Def_QKPSDP_SQKEFeasible

open Matrix

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, (SQKE), p.2: `(x, X)` (equivalently `Y = (1 x⊤; x X)`) is a
*global optimal solution* of `(SQKE) min { −⟨C, X⟩ : a⊤Xa − τa⊤x = 0, diag(X) = x, Y ∈ S₊ⁿ⁺¹ }`:
it is feasible and its objective `−⟨C, X⟩` is at most that of every feasible `(x', X')`.

**Formalization Note** `⟨A, B⟩ := Tr(AB⊤)` (p.4) is `(A * Bᵀ).trace`. -/
def IsGlobalOptSQKE {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (τ : ℝ)
    (x : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  SQKEFeasible a τ x X ∧
    ∀ (x' : Fin n → ℝ) (X' : Matrix (Fin n) (Fin n) ℝ), SQKEFeasible a τ x' X' →
      -(C * Xᵀ).trace ≤ -(C * X'ᵀ).trace

end QKPSDP


