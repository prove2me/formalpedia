-- Prove2me | Definitions.Def_BorderDiffEq_derivMatrix
-- name    : BorderDiffEq_derivMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:26:44.12651+00:00
-- url     : https://prove2.me/theorems/e4cc64e1-0dd4-42b9-a2f8-595a065ef002
-- title:
--   The $r\times(r+1)$ matrix $(D^jS_i)$ of Lemmas 4.4 and 5.1
-- statement:
--   For polynomials $S_1,\dots,S_r$ in $z$ (over a commutative ring) and $D=\partial/\partial z$, let
--   $$
--   M=\begin{pmatrix} S_1 & DS_1 & D^2S_1 & \cdots & D^rS_1\\ \vdots & \vdots & \vdots & & \vdots\\ S_r & DS_r & D^2S_r & \cdots & D^rS_r\end{pmatrix},
--   $$
--   an $r\times(r+1)$ matrix. Deleting its last column gives the Wronskian matrix of $S_1,\dots,S_r$.
--
--   **Formalization Note** Rows are `Fin r` and columns `Fin (r+1)`; column $j$ (0-based) is the paper's $(j+1)$-st column and holds $D^jS_i$.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Lemma 4.4, p.25; Lemma 5.1, p.31

import Mathlib

namespace BorderDiffEq

/-- **The `r × (r+1)` matrix `M` of Lemmas 4.4 and 5.1** (Bhat–Dutta–Kaplan–Shpilka–Shringi,
*Demystifying Border of Structured Algebraic Circuits via Differential Equations*, manuscript (STOC
2027 submission), Lemma 4.4, p.25, and Lemma 5.1, p.31): the matrix whose `i`-th row is
`(Sᵢ, D Sᵢ, D² Sᵢ, …, D^r Sᵢ)`, `D = ∂/∂z`.

**Formalization Note.** Rows are `Fin r`, columns `Fin (r+1)` (0-based: column `j` holds `D^j Sᵢ`,
the paper's `(j+1)`-st column); `D` is `Polynomial.derivative`. -/
noncomputable def derivMatrix {A : Type} [CommRing A] {r : ℕ} (S : Fin r → Polynomial A) :
    Matrix (Fin r) (Fin (r + 1)) (Polynomial A) :=
  Matrix.of fun i j => Polynomial.derivative^[(j : ℕ)] (S i)

end BorderDiffEq


