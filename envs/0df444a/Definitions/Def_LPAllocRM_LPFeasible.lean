-- Prove2me | Definitions.Def_LPAllocRM_LPFeasible
-- name    : LPAllocRM_LPFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:02.506928+00:00
-- url     : https://prove2.me/theorems/3551f70e-b9b3-46b5-a851-7d5673fec9df
-- title:
--   Feasible points of the bounded LP $\max\{f\cdot x : Ax\le b,\ 0\le x\le u\}$
-- statement:
--   Let $A$ be a real $m\times n$ matrix, $b\in\mathbb R^m$ and $u\in\mathbb R^n$. A vector $x\in\mathbb R^n$ is **feasible** for the linear program
--
--   $$\max_x\ \{f\cdot x : Ax\le b,\ 0\le x\le u\}$$
--
--   if $Ax\le b$, $x\ge 0$ and $x\le u$ hold componentwise.
--
--   The paper's linear program (3) is the instance $(b,u)=(c,\mu)$, and the $k$th linear program (6) is the instance $(b,u)=(kc,k\mu)$.
--
--   **Formalization Note** Vectors are functions on `Fin n`; vector inequalities are componentwise.
-- source:
--   Cooper, Asymptotic Behavior of an Allocation Policy for Revenue Management, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855, eq. (3), p.723 and eq. (6), p.723

import Mathlib
open Matrix

namespace LPAllocRM

/-- Feasibility for the bounded linear program `max {f · x : A x ≤ b, 0 ≤ x ≤ u}`: a vector
`x : Fin n → ℝ` is feasible if `A x ≤ b` componentwise and `0 ≤ x ≤ u` componentwise.
Cooper, *Asymptotic Behavior of an Allocation Policy for Revenue Management*, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855,
LP (3), p.723 (PDF p.4), with `(b, u) = (c, μ)`, and the kth LP (6), p.723 (PDF p.4), with
`(b, u) = (k c, k μ)`.

**Formalization Note** The general LP is its own object; the paper's (3) and (6) are the instances
`(b, u) = (c, μ)` and `(k • c, k • μ)`. Vectors are functions `Fin n → ℝ`, and the vector
inequalities `0 ≤ x`, `x ≤ u` are the componentwise (Pi) order. -/
def LPFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (u : Fin n → ℝ)
    (x : Fin n → ℝ) : Prop :=
  (∀ i, (A *ᵥ x) i ≤ b i) ∧ 0 ≤ x ∧ x ≤ u

end LPAllocRM


