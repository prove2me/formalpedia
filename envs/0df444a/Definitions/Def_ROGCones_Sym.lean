-- Prove2me | Definitions.Def_ROGCones_Sym
-- name    : ROGCones_Sym
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:05.041793+00:00
-- url     : https://prove2.me/theorems/9277fb7f-6490-4e9f-ad39-228b2836bcba
-- title:
--   $\mathrm{Sym}(M) = (M + M^\top)/2$, the symmetric part of a matrix
-- statement:
--   For a real $n\times n$ matrix $M$, its **symmetric part** is
--   $$
--   \mathrm{Sym}(M) := \frac{M + M^\top}{2} \in \mathbb S^n .
--   $$
--   The paper applies it to outer products: for $a, c \in \mathbb R^n$, $\mathrm{Sym}(ac^\top) = (ac^\top + ca^\top)/2$ is the symmetric matrix of the bilinear quantity $a^\top X c = \langle \mathrm{Sym}(ac^\top), X\rangle$ for symmetric $X$. These matrices appear in condition (ii) of the main theorem.
--
--   **Formalization Note** Matrices are `Matrix (Fin n) (Fin n) ℝ`; the outer product $ac^\top$ is `Matrix.vecMulVec a c`.
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, §1.4 Notation, p.5

import Mathlib

namespace ROGCones

/-- **Symmetric part of a square matrix**, `Sym(M) := (M + Mᵀ)/2`.
Argue, Kılınç-Karzan & Wang, *Necessary and sufficient conditions for rank-one generated cones*,
arXiv:2007.07433v2, §1.4 Notation, p.5: "For M ∈ ℝⁿˣⁿ, let Sym(M) := (M + M⊤)/2 ∈ Sⁿ."

**Formalization Note.** `n × n` real matrices are `Matrix (Fin n) (Fin n) ℝ`; the division by 2
is the scalar `(1/2 : ℝ)`. The paper applies it to outer products: `Sym(acᵀ)` is
`Sym (Matrix.vecMulVec a c)`, which equals `(acᵀ + caᵀ)/2`. -/
noncomputable def Sym {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • (M + M.transpose)

end ROGCones


