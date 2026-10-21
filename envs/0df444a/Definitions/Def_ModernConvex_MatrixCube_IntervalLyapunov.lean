-- Prove2me | Definitions.Def_ModernConvex_MatrixCube_IntervalLyapunov
-- name    : ModernConvex_MatrixCube_IntervalLyapunov
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:04.050778+00:00
-- url     : https://prove2.me/theorems/d2e9d284-be88-4137-938c-09fca50df7c3
-- title:
--   Interval Lyapunov: the interval matrix 𝒰_ρ, the systems (Ly[ρ]) and (A[ρ]), and the radii R[A*, D], ρ[A*, D]
-- statement:
--   This file fixes the objects of the interval Lyapunov stability problem (Ben-Tal–Nemirovski, §4.4.3, pp. 189, 194–195).
--
--   1. A real $n\times n$ matrix $A$ is **stable** if all its (complex) eigenvalues lie in the open left half-plane (p. 194, footnote 30).
--   2. Given a nominal matrix $A^*$, a scale matrix $D$ with nonnegative entries and a level $\rho$, the **interval matrix** (4.4.33) is
--   $$\mathcal U_\rho=\{A\in\mathbf M^{n,n} : |A_{ij}-A^*_{ij}|\le\rho D_{ij},\ i,j=1,\dots,n\}.$$
--   3. $X\in\mathbf S^n$ **solves $(\mathrm{Ly}[\rho])$** if $X\succeq I$ and $A^TX+XA\preceq -I$ for every $A\in\mathcal U_\rho$.
--   4. With $\mathcal D=\{(i,j): D_{ij}>0\}$ and $E^{ij}$ the basic matrix (its $ij$th entry is $1$, all others $0$), symmetric matrices $X$ and $X^{ij}$, $(i,j)\in\mathcal D$, **solve $(\mathrm A[\rho])$** if
--   $$X\succeq I,\qquad X^{ij}\succeq-\rho D_{ij}\big[[E^{ij}]^TX+XE^{ij}\big],\quad X^{ij}\succeq\rho D_{ij}\big[[E^{ij}]^TX+XE^{ij}\big],\ (i,j)\in\mathcal D,\qquad \sum_{(i,j)\in\mathcal D}X^{ij}\preceq -I-[A^*]^TX-XA^*.$$
--   5. $R[A^*,D]$ is the supremum of those $\rho\ge0$ for which $(\mathrm{Ly}[\rho])$ is solvable, and $\rho[A^*,D]$ the supremum of those $\rho\ge0$ for which $(\mathrm A[\rho])$ is solvable, both in $[-\infty,+\infty]$.
--
--   These are the objects of Proposition 4.4.6.
--
--   **Formalization Note** Stability is stated through the complex spectrum of the real matrix mapped into $\mathbb C^{n\times n}$. The family $X^{ij}$ is indexed by all pairs $(i,j)$; only its members with $(i,j)\in\mathcal D$ enter the system. $E^{ij}$ is Mathlib's `Matrix.single i j 1`. The radii are `sSup`s in `EReal`. The book's sum in $(\mathrm A[\rho])$ carries a stray upper index $n$, which is ignored.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 189 (4.4.33), p. 194 Interval Lyapunov and footnote 30, p. 195 (A[ρ])

import Mathlib

open Matrix

namespace ModernConvex.MatrixCube

/-- A real `n × n` matrix `A` is stable (p. 194, footnote 30): all its eigenvalues lie in the open
left half-plane, i.e. every complex eigenvalue `λ` of `A` has `Re λ < 0`. -/
def IsStable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)), z.re < 0

/-- The interval matrix (4.4.33), p. 189 and p. 194:
`𝒰_ρ = { A ∈ M^{n,n} | |Aᵢⱼ − A*ᵢⱼ| ≤ ρDᵢⱼ, i, j = 1, …, n }`. -/
def intervalMatrix {n : ℕ} (Astar D : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  {A | ∀ i j, |A i j - Astar i j| ≤ ρ * D i j}

/-- `X ∈ Sⁿ` solves the semi-infinite system of LMIs `(Ly[ρ])`, p. 194:
`X ⪰ I; AᵀX + XA ⪯ −I ∀A ∈ 𝒰_ρ`. -/
def IsLySolution {n : ℕ} (Astar D : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  X.IsHermitian ∧ (X - 1).PosSemidef ∧
    ∀ A ∈ intervalMatrix Astar D ρ, (-1 - (Aᵀ * X + X * A)).PosSemidef

/-- The system `(Ly[ρ])` is solvable. -/
def LySolvable {n : ℕ} (Astar D : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) : Prop :=
  ∃ X : Matrix (Fin n) (Fin n) ℝ, IsLySolution Astar D ρ X

/-- The index set `𝒟 = {(i, j) : Dᵢⱼ > 0}` (p. 195). -/
noncomputable def posEntries {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => 0 < D p.1 p.2

/-- The basic matrix `Eⁱʲ` (p. 195): its `ij`th entry is `1`, all other entries are zero. -/
def basicMatrix {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.single i j 1

/-- `(X, (Xⁱʲ)_{(i,j)∈𝒟})` solves the system of LMIs `(A[ρ])`, p. 195:
`X ⪰ I`,
`Xⁱʲ ⪰ −ρDᵢⱼ[[Eⁱʲ]ᵀX + XEⁱʲ], Xⁱʲ ⪰ ρDᵢⱼ[[Eⁱʲ]ᵀX + XEⁱʲ], (i, j) ∈ 𝒟`,
`∑_{(i,j)∈𝒟} Xⁱʲ ⪯ −I − [A*]ᵀX − XA*`,
with `X, Xⁱʲ ∈ Sⁿ`. The family `Y` is indexed by all pairs `(i, j)`; only its members with
`(i, j) ∈ 𝒟` enter the system. -/
def IsASolution {n : ℕ} (Astar D : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) (Y : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  X.IsHermitian ∧ (X - 1).PosSemidef ∧
    (∀ p ∈ posEntries D,
      (Y p.1 p.2).IsHermitian ∧
      (Y p.1 p.2 - (-ρ * D p.1 p.2) •
          ((basicMatrix p.1 p.2)ᵀ * X + X * basicMatrix p.1 p.2)).PosSemidef ∧
      (Y p.1 p.2 - (ρ * D p.1 p.2) •
          ((basicMatrix p.1 p.2)ᵀ * X + X * basicMatrix p.1 p.2)).PosSemidef) ∧
    (-1 - Astarᵀ * X - X * Astar - ∑ p ∈ posEntries D, Y p.1 p.2).PosSemidef

/-- The system `(A[ρ])` is solvable. -/
def ASolvable {n : ℕ} (Astar D : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) : Prop :=
  ∃ (X : Matrix (Fin n) (Fin n) ℝ) (Y : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ),
    IsASolution Astar D ρ X Y

/-- `R[A*, D]` (p. 194): the supremum of those `ρ ≥ 0` for which `(Ly[ρ])` is solvable, in
`[−∞, +∞]`. -/
noncomputable def lyapRadius {n : ℕ} (Astar D : Matrix (Fin n) (Fin n) ℝ) : EReal :=
  sSup {r : EReal | ∃ ρ : ℝ, r = ρ ∧ 0 ≤ ρ ∧ LySolvable Astar D ρ}

/-- `ρ[A*, D]` (p. 195): the supremum of those `ρ ≥ 0` for which `(A[ρ])` is solvable, in
`[−∞, +∞]`. -/
noncomputable def lmiRadius {n : ℕ} (Astar D : Matrix (Fin n) (Fin n) ℝ) : EReal :=
  sSup {r : EReal | ∃ ρ : ℝ, r = ρ ∧ 0 ≤ ρ ∧ ASolvable Astar D ρ}

end ModernConvex.MatrixCube


