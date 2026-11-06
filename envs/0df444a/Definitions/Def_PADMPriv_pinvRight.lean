-- Prove2me | Definitions.Def_PADMPriv_pinvRight
-- name    : PADMPriv_pinvRight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:50.988213+00:00
-- url     : https://prove2.me/theorems/08ac24d8-93f4-46f2-8c08-b68fc52e3606
-- title:
--   Right inverse $V = A^\top(AA^\top)^{-1}$ of a full-row-rank matrix
-- statement:
--   For a matrix $A \in \mathbb R^{m\times p}$ define
--   $$
--   V := A^\top (AA^\top)^{-1} \in \mathbb R^{p\times m}.
--   $$
--   When $A$ has full row rank, $AA^\top$ is invertible and $AV = I_m$, so $x = Vu$ recovers a preimage of $u$ under $A$ lying in $\operatorname{range}(A^\top)$. The same formula applied to $B$ gives $U := B^\top(BB^\top)^{-1}$. These maps turn the image-space iterate of PADM into a feasible pair $(Vu, U(c-u))$.
--
--   **Formalization Note** Matrices are real matrices indexed by `Fin`; the inverse is Mathlib's matrix inverse, which is $0$ for a singular matrix; every statement using $V$ assumes full row rank.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Eq. (12), p.6

import Mathlib

namespace PADMPriv

/-- The right inverse `V := Aᵀ(AAᵀ)⁻¹` of a full-row-rank matrix `A ∈ ℝ^{m×p}` (Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d),
Eq. (12), p.6; the same formula with `B` gives `U := Bᵀ(BBᵀ)⁻¹`). When `A` has full row rank,
`AAᵀ` is invertible and `AV = I_m`.

**Formalization Note** Matrices are `Matrix (Fin m) (Fin p) ℝ`; the inverse is Mathlib's
`Matrix.inv` (junk `0` when `AAᵀ` is singular, which full row rank excludes in every use). -/
noncomputable def pinvRight {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) : Matrix (Fin p) (Fin m) ℝ :=
  A.transpose * (A * A.transpose)⁻¹

end PADMPriv


