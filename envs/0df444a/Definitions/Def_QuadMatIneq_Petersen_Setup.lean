-- Prove2me | Definitions.Def_QuadMatIneq_Petersen_Setup
-- name    : QuadMatIneq_Petersen_Setup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T19:15:52.780269+00:00
-- url     : https://prove2.me/theorems/9237564e-2554-4dcd-8825-a04c5c42608c
-- title:
--   Proposition 4.16, (4.17) — the uncertainty set $\mathcal F=\{F: F^\top F\leqslant\bar F\}$ and the matrices $M$, $N$ of Petersen's lemma
-- statement:
--   Fix sizes $n,p,q$. For a matrix $\bar F\in\mathbb R^{q\times q}$ the **norm-bounded uncertainty set** of Petersen's lemma is
--   $$\mathcal F:=\{F\in\mathbb R^{p\times q}\mid F^\top F\leqslant\bar F\},$$
--   where $F^\top F\leqslant \bar F$ means that $\bar F-F^\top F$ is symmetric positive semidefinite.
--
--   For $C\in\mathbb R^{n\times n}$, $E\in\mathbb R^{n\times p}$ and $G\in\mathbb R^{q\times n}$, display (4.17) of the paper defines the $(n+p)\times(n+p)$ block matrices
--   $$M:=\begin{bmatrix}-C&-E\\-E^\top&0\end{bmatrix},\qquad N:=\begin{bmatrix}G^\top\bar FG&0\\0&-I\end{bmatrix},$$
--   partitioned with upper-left block of size $n\times n$ and lower-right block of size $p\times p$.
--
--   With these matrices the robust inequalities of Petersen's lemma become inclusions of quadratic-matrix-inequality solution sets, $\mathcal Z_p(N)\subseteq\mathcal Z_p^+(M)$ or $\mathcal Z_p(N)\subseteq\mathcal Z_p(M)$, so that the matrix S-lemmas apply.
--
--   **Formalization Note** The three sizes are arbitrary finite types; in the theorems they are `Fin n`, `Fin p`, `Fin q`. The block matrices are built with Mathlib's `fromBlocks`, with the first summand of the index type being the $n$-block.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Proposition 4.16 (definition of 𝓕), p. 17; display (4.17), p. 17

import Mathlib

namespace QuadMatIneq.Petersen

open Matrix

/-- The uncertainty set `𝓕 := {F ∈ ℝ^{p×q} | FᵀF ⩽ F̄}` of Proposition 4.16. -/
def uncSet {p q : Type*} [Fintype p] [Fintype q] (Fbar : Matrix q q ℝ) :
    Set (Matrix p q ℝ) :=
  {F | (Fbar - Fᵀ * F).PosSemidef}

/-- `M := [−C −E; −Eᵀ 0]` of (4.17), partitioned as `n + p`. -/
def petersenM {n p : Type*} (C : Matrix n n ℝ) (E : Matrix n p ℝ) :
    Matrix (n ⊕ p) (n ⊕ p) ℝ :=
  Matrix.fromBlocks (-C) (-E) (-Eᵀ) 0

/-- `N := [GᵀF̄G 0; 0 −I]` of (4.17), partitioned as `n + p`. -/
def petersenN {n p q : Type*} [Fintype q] [DecidableEq p] (Fbar : Matrix q q ℝ)
    (G : Matrix q n ℝ) : Matrix (n ⊕ p) (n ⊕ p) ℝ :=
  Matrix.fromBlocks (Gᵀ * Fbar * G) 0 0 (-1)

end QuadMatIneq.Petersen


