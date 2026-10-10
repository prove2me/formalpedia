-- Prove2me | Definitions.Def_QuadMatIneq_Finsler_QMI
-- name    : QuadMatIneq_Finsler_QMI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:12:12.430039+00:00
-- url     : https://prove2.me/theorems/a7809ef6-c2a4-4c46-b4ae-f133b4dfc35f
-- title:
--   (4.4) and the proof of Theorem 4.8, p. 12 — the matrices $\Theta$ and $T=[I\ 0;\ -N_{22}^\dagger N_{21}\ I]$ of Matrix Finsler's lemma
-- statement:
--   This file adds, on top of the shared quadratic-matrix-inequality layer of van Waarde, Camlibel, Eising and Trentelman (the module `QuadMatIneq.Basic.QMI`: the Moore–Penrose pseudo-inverse $A^\dagger$, the quadratic form $\begin{bmatrix}I_q\\ Z\end{bmatrix}^\top\Pi\begin{bmatrix}I_q\\ Z\end{bmatrix}$, the sets $\mathcal Z_r(\Pi)$, $\mathcal Z_r^+(\Pi)$, $\mathcal Z_r^0(\Pi)$, the generalized Schur complement $\Pi\,|\,\Pi_{22}$ and the class $\boldsymbol\Pi_{q,r}$), the two matrices used in Matrix Finsler's lemma. All matrices are real.
--
--   Let $M,N\in\mathbb S^{q+r}$ be partitioned as $M=\begin{bmatrix}M_{11}&M_{12}\\ M_{21}&M_{22}\end{bmatrix}$, $N=\begin{bmatrix}N_{11}&N_{12}\\ N_{21}&N_{22}\end{bmatrix}$ with $M_{11},N_{11}$ of size $q\times q$ and $M_{22},N_{22}$ of size $r\times r$ ((4.1), p. 10). Define
--   $$\Theta:=\begin{bmatrix}I\\ -N_{22}^\dagger N_{21}\end{bmatrix}^\top M\begin{bmatrix}I\\ -N_{22}^\dagger N_{21}\end{bmatrix}\in\mathbb R^{q\times q}\quad\text{(4.4)},\qquad T:=\begin{bmatrix}I&0\\ -N_{22}^\dagger N_{21}&I\end{bmatrix}\in\mathbb R^{(q+r)\times(q+r)} .$$
--
--   $\Theta$ enters the hypothesis $\ker\Theta\subseteq\ker M\,|\,M_{22}$ of Matrix Finsler's lemma (Theorem 4.8), and $T$ is the congruence used in its proof.
--
--   **Formalization Note** $\Theta$ is written as the shared quadratic form of $M$ evaluated at $Z=-N_{22}^\dagger N_{21}$, which is literally (4.4); the pseudo-inverse is the shared `pinv` (Hilbert's $\varepsilon$ over the four Penrose conditions, hence exactly $A^\dagger$). The blocks are indexed by arbitrary finite types `ι` (size $q$) and `κ` (size $r$).
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, (4.1) p. 10; (4.4) p. 12 and the matrix T in the proof of Theorem 4.8, p. 12

import Mathlib
import Definitions.Def_QuadMatIneq_Basic_QMI

namespace QuadMatIneq.Finsler

open Matrix

section QMI

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- `Θ := [I; −N₂₂†N₂₁]ᵀ M [I; −N₂₂†N₂₁]` of (4.4), written as the quadratic form `qmiForm M Z`
at `Z = −N₂₂†N₂₁`. -/
noncomputable def Theta (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Matrix ι ι ℝ :=
  QuadMatIneq.Basic.qmiForm M (-(QuadMatIneq.Basic.pinv N.toBlocks₂₂) * N.toBlocks₂₁)

/-- The congruence matrix `T := [I 0; −N₂₂†N₂₁ I]` of the proof of Theorem 4.8. -/
noncomputable def Tmat (N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  Matrix.fromBlocks 1 0 (-(QuadMatIneq.Basic.pinv N.toBlocks₂₂) * N.toBlocks₂₁) 1

end QMI

end QuadMatIneq.Finsler


