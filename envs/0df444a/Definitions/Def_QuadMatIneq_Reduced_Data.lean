-- Prove2me | Definitions.Def_QuadMatIneq_Reduced_Data
-- name    : QuadMatIneq_Reduced_Data
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:59:00.984981+00:00
-- url     : https://prove2.me/theorems/aa23f03f-cc94-441b-bb31-2807b5457e1c
-- title:
--   §2, §5.1–5.2 — noisy input-state data, the set Σ of consistent systems, informativity for quadratic stabilization, the LMIs (5.5), (5.6), (5.9a)–(5.11b) and the gain (5.10)
-- statement:
--   This file encodes the data-driven stabilization setting of Section 2 and the matrices of Theorems 5.1 and 5.3.
--
--   **Data.** An unknown system $x(t+1) = A_s x(t) + B_s u(t) + w(t)$ with $x, w\in\mathbb R^n$, $u\in\mathbb R^m$ is sampled, giving
--   $$X = [x(0)\ x(1)\ \cdots\ x(T)],\qquad U_- = [u(0)\ \cdots\ u(T-1)],$$
--   and $X_- = [x(0)\ \cdots\ x(T-1)]$, $X_+ = [x(1)\ \cdots\ x(T)]$. The unknown noise $W_- = [w(0)\ \cdots\ w(T-1)]$ is assumed to satisfy the QMI
--   $$\begin{bmatrix} I\\ W_-^\top\end{bmatrix}^\top \Phi \begin{bmatrix} I\\ W_-^\top\end{bmatrix}\ge 0,\qquad \Phi = \begin{bmatrix}\Phi_{11}&\Phi_{12}\\ \Phi_{21}&\Phi_{22}\end{bmatrix}\in\mathbb S^{n+T},$$
--   i.e. $W_-^\top \in \mathcal Z_T(\Phi)$. The set of systems consistent with the data is
--   $$\Sigma = \{(A,B)\in\mathbb R^{n\times n}\times\mathbb R^{n\times m} : X_+ = AX_- + BU_- + W_- \text{ for some } W_- \text{ with } W_-^\top\in\mathcal Z_T(\Phi)\}.$$
--
--   **Informativity (Definition 2.1).** The data $(U_-, X)$ are informative for quadratic stabilization if there exist $K\in\mathbb R^{m\times n}$ and $P>0$ such that $P - (A+BK)P(A+BK)^\top > 0$ for all $(A,B)\in\Sigma$.
--
--   **The LMIs of Theorem 5.1.** With block rows and columns of sizes $n, n, m, n$,
--   $$\text{(5.5)}\quad \begin{bmatrix} P-\beta I&0&0&0\\ 0&-P&-L^\top&0\\ 0&-L&0&L\\ 0&0&L^\top&P\end{bmatrix} - \begin{bmatrix} I&X_+\\ 0&-X_-\\ 0&-U_-\\ 0&0\end{bmatrix}\Phi\begin{bmatrix} I&X_+\\ 0&-X_-\\ 0&-U_-\\ 0&0\end{bmatrix}^\top,$$
--   and (5.6) is the same matrix with $P$ in place of $P - \beta I$ in the top-left block.
--
--   **The reduced LMIs of Theorem 5.3.** With $\Theta := \Phi_{12} + X_+\Phi_{22}$ and $V := \begin{bmatrix} X_-\\ U_-\end{bmatrix}$:
--   $$\text{(5.9a)}\quad P-\beta I-[I\ \ X_+]\,\Phi\begin{bmatrix} I\\ X_+^\top\end{bmatrix} + \Theta V^\top\big(V\Phi_{22}V^\top\big)^\dagger V\Theta^\top,$$
--   $$\text{(5.9b)}\quad \begin{bmatrix} P-\beta I&0\\ 0&-P\end{bmatrix} - \begin{bmatrix} I&X_+\\ 0&-X_-\end{bmatrix}\Phi\begin{bmatrix} I&X_+\\ 0&-X_-\end{bmatrix}^\top;$$
--   (5.11a) is (5.9a) with $\beta = 0$ and the ordinary inverse $(V\Phi_{22}V^\top)^{-1}$ in place of the pseudo-inverse, and (5.11b) is (5.9b) with $\beta = 0$. Finally, $\Gamma = P - \beta I - [I\ \ X_+]\Phi[I\ \ X_+]^\top$ in part (a) and $\Gamma = P - [I\ \ X_+]\Phi[I\ \ X_+]^\top$ in part (b), and the gain (5.10) is
--   $$K = \big(U_-(\Phi_{22}+\Theta^\top\Gamma^\dagger\Theta)X_-^\top\big)\big(X_-(\Phi_{22}+\Theta^\top\Gamma^\dagger\Theta)X_-^\top\big)^\dagger.$$
--
--   **Formalization Note** $X$ is an $n\times(T+1)$ matrix and $X_-$, $X_+$ are its first and last $T$ columns. Block matrices are built from Mathlib's `fromBlocks`/`fromRows`/`fromCols` over sum index types. The gain (5.10) takes $\Gamma$ as an argument, so the same definition serves both parts of Theorem 5.3. The inverse in (5.11a) is Mathlib's total inverse, which is the true inverse under the hypotheses of Theorem 5.3(b), where it is used.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, §2 pp. 3–4, (2.1)–(2.4), Definition 2.1; Theorem 5.1 (5.5), (5.6), pp. 18–19; Theorem 5.3 (5.9a)–(5.11b), (5.10), pp. 20–21

import Mathlib
import Definitions.Def_QuadMatIneq_Reduced_QMI
import Definitions.Def_QuadMatIneq_Stabilization_Data

namespace QuadMatIneq.Reduced

open Matrix

variable {n m T : ℕ}

/-! ### The LMIs (5.5) and (5.6) of Theorem 5.1 (block rows/columns `n | n | m | n`) -/

/-- The data factor `[I X₊; 0 −X₋; 0 −U₋; 0 0]` of (5.5)/(5.6). -/
def dataFactor (X : Matrix (Fin n) (Fin (T + 1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ) :
    Matrix ((Fin n ⊕ Fin n) ⊕ (Fin m ⊕ Fin n)) (Fin n ⊕ Fin T) ℝ :=
  Matrix.fromRows (Matrix.fromBlocks 1 (QuadMatIneq.Stabilization.Xplus X) 0 (-QuadMatIneq.Stabilization.Xminus X)) (Matrix.fromBlocks 0 (-Um) 0 0)

/-- The block matrix `[P − βI 0 0 0; 0 −P −Lᵀ 0; 0 −L 0 L; 0 0 Lᵀ P]` of (5.5). -/
def blk55 (P : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin m) (Fin n) ℝ) (β : ℝ) :
    Matrix ((Fin n ⊕ Fin n) ⊕ (Fin m ⊕ Fin n)) ((Fin n ⊕ Fin n) ⊕ (Fin m ⊕ Fin n)) ℝ :=
  Matrix.fromBlocks (Matrix.fromBlocks (P - β • 1) 0 0 (-P)) (Matrix.fromBlocks 0 0 (-Lᵀ) 0)
    (Matrix.fromBlocks 0 (-L) 0 0) (Matrix.fromBlocks 0 L Lᵀ P)

/-- The block matrix `[P 0 0 0; 0 −P −Lᵀ 0; 0 −L 0 L; 0 0 Lᵀ P]` of (5.6). -/
def blk56 (P : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin m) (Fin n) ℝ) :
    Matrix ((Fin n ⊕ Fin n) ⊕ (Fin m ⊕ Fin n)) ((Fin n ⊕ Fin n) ⊕ (Fin m ⊕ Fin n)) ℝ :=
  Matrix.fromBlocks (Matrix.fromBlocks P 0 0 (-P)) (Matrix.fromBlocks 0 0 (-Lᵀ) 0)
    (Matrix.fromBlocks 0 (-L) 0 0) (Matrix.fromBlocks 0 L Lᵀ P)

/-- The left-hand side of (5.5). -/
def lmi55 (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ) (X : Matrix (Fin n) (Fin (T + 1)) ℝ)
    (Um : Matrix (Fin m) (Fin T) ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (L : Matrix (Fin m) (Fin n) ℝ) (β : ℝ) :
    Matrix ((Fin n ⊕ Fin n) ⊕ (Fin m ⊕ Fin n)) ((Fin n ⊕ Fin n) ⊕ (Fin m ⊕ Fin n)) ℝ :=
  blk55 P L β - dataFactor X Um * Φ * (dataFactor X Um)ᵀ

/-! ### The reduced LMIs (5.9a)–(5.11b) and the gain (5.10) of Theorem 5.3 -/

/-- `[X₋; U₋] ∈ ℝ^{(n+m)×T}`. -/
def Vmat (X : Matrix (Fin n) (Fin (T + 1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ) :
    Matrix (Fin n ⊕ Fin m) (Fin T) ℝ :=
  Matrix.fromRows (QuadMatIneq.Stabilization.Xminus X) Um

/-- `Θ := Φ₁₂ + X₊ Φ₂₂ ∈ ℝ^{n×T}` (Theorem 5.3). -/
def Theta (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ) (X : Matrix (Fin n) (Fin (T + 1)) ℝ) :
    Matrix (Fin n) (Fin T) ℝ :=
  Φ.toBlocks₁₂ + QuadMatIneq.Stabilization.Xplus X * Φ.toBlocks₂₂

/-- `[I X₊] ∈ ℝ^{n×(n+T)}`. -/
def IXplus (X : Matrix (Fin n) (Fin (T + 1)) ℝ) : Matrix (Fin n) (Fin n ⊕ Fin T) ℝ :=
  Matrix.fromCols 1 (QuadMatIneq.Stabilization.Xplus X)

/-- `Γ = P − βI − [I X₊] Φ [I; X₊ᵀ]`, Theorem 5.3(a). -/
def Gamma (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ) (X : Matrix (Fin n) (Fin (T + 1)) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  P - β • 1 - IXplus X * Φ * (IXplus X)ᵀ

/-- `Γ = P − [I X₊] Φ [I; X₊ᵀ]`, Theorem 5.3(b). -/
def GammaB (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ) (X : Matrix (Fin n) (Fin (T + 1)) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  P - IXplus X * Φ * (IXplus X)ᵀ

/-- The left-hand side of (5.9a):
`P − βI − [I X₊]Φ[I; X₊ᵀ] + Θ [X₋; U₋]ᵀ ([X₋; U₋] Φ₂₂ [X₋; U₋]ᵀ)† [X₋; U₋] Θᵀ`. -/
noncomputable def lmi59a (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ)
    (X : Matrix (Fin n) (Fin (T + 1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Gamma Φ X P β + Theta Φ X * (Vmat X Um)ᵀ *
    pinv (Vmat X Um * Φ.toBlocks₂₂ * (Vmat X Um)ᵀ) * Vmat X Um * (Theta Φ X)ᵀ

/-- The data factor `[I X₊; 0 −X₋]` of (5.9b)/(5.11b). -/
def dataFactor2 (X : Matrix (Fin n) (Fin (T + 1)) ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin T) ℝ :=
  Matrix.fromBlocks 1 (QuadMatIneq.Stabilization.Xplus X) 0 (-QuadMatIneq.Stabilization.Xminus X)

/-- The left-hand side of (5.9b): `[P − βI 0; 0 −P] − [I X₊; 0 −X₋] Φ [I X₊; 0 −X₋]ᵀ`. -/
def lmi59b (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ) (X : Matrix (Fin n) (Fin (T + 1)) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.fromBlocks (P - β • 1) 0 0 (-P) - dataFactor2 X * Φ * (dataFactor2 X)ᵀ

/-- The left-hand side of (5.11a):
`P − [I X₊]Φ[I; X₊ᵀ] + Θ [X₋; U₋]ᵀ ([X₋; U₋] Φ₂₂ [X₋; U₋]ᵀ)⁻¹ [X₋; U₋] Θᵀ`. -/
noncomputable def lmi511a (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ)
    (X : Matrix (Fin n) (Fin (T + 1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  GammaB Φ X P + Theta Φ X * (Vmat X Um)ᵀ *
    (Vmat X Um * Φ.toBlocks₂₂ * (Vmat X Um)ᵀ)⁻¹ * Vmat X Um * (Theta Φ X)ᵀ

/-- The left-hand side of (5.11b): `[P 0; 0 −P] − [I X₊; 0 −X₋] Φ [I X₊; 0 −X₋]ᵀ`. -/
def lmi511b (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ) (X : Matrix (Fin n) (Fin (T + 1)) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.fromBlocks P 0 0 (-P) - dataFactor2 X * Φ * (dataFactor2 X)ᵀ

/-- The gain (5.10), for a given `Γ`:
`K = (U₋(Φ₂₂ + ΘᵀΓ†Θ)X₋ᵀ)(X₋(Φ₂₂ + ΘᵀΓ†Θ)X₋ᵀ)†`. -/
noncomputable def gain510 (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ)
    (X : Matrix (Fin n) (Fin (T + 1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ)
    (Γ : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  (Um * (Φ.toBlocks₂₂ + (Theta Φ X)ᵀ * pinv Γ * Theta Φ X) * (QuadMatIneq.Stabilization.Xminus X)ᵀ) *
    pinv (QuadMatIneq.Stabilization.Xminus X * (Φ.toBlocks₂₂ + (Theta Φ X)ᵀ * pinv Γ * Theta Φ X) * (QuadMatIneq.Stabilization.Xminus X)ᵀ)

end QuadMatIneq.Reduced


