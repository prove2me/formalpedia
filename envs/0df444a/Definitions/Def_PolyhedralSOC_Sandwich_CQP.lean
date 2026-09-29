-- Prove2me | Definitions.Def_PolyhedralSOC_Sandwich_CQP
-- name    : PolyhedralSOC_Sandwich_CQP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:51:03.29653+00:00
-- url     : https://prove2.me/theorems/59f80933-907c-43e2-877a-82b572702555
-- title:
--   Conic quadratic problem (CQP), its ε-relaxation (CQP_ε), and their feasible sets
-- statement:
--   For a vector $y\in\mathbb R^k$ write $\|y\|_2=\sqrt{y^Ty}=\sqrt{y_1^2+\dots+y_k^2}$ for its Euclidean norm.
--
--   A **conic quadratic problem** in the variable $x\in\mathbb R^n$ is
--   $$
--   \text{(CQP)}\qquad \min_x\bigl\{e^Tx \bigm| Ax\ge b,\ \|A_\ell x-b_\ell\|_2\le c_\ell^Tx-d_\ell,\ \ell=1,\dots,m\bigr\},
--   $$
--   where $e\in\mathbb R^n$, $A$ is a $k_0\times n$ matrix, $b\in\mathbb R^{k_0}$ (the inequality $Ax\ge b$ is componentwise), and for each of the $m$ conic constraints $A_\ell$ is a $k_\ell\times n$ matrix, $b_\ell\in\mathbb R^{k_\ell}$, $c_\ell\in\mathbb R^n$ and $d_\ell\in\mathbb R$. The row sizes $k_\ell$ may differ from one constraint to the next.
--
--   For $\varepsilon>0$ its **$\varepsilon$-relaxation** is
--   $$
--   \text{(CQP}_\varepsilon)\qquad \min_x\bigl\{e^Tx \bigm| Ax\ge b,\ \|A_\ell x-b_\ell\|_2\le (1+\varepsilon)\bigl[c_\ell^Tx-d_\ell\bigr],\ \ell=1,\dots,m\bigr\}.
--   $$
--
--   Three objects are defined: the problem data, the feasible set $\mathrm{Feas}(\mathrm{CQP})\subseteq\mathbb R^n$, and the feasible set $\mathrm{Feas}(\mathrm{CQP}_\varepsilon)\subseteq\mathbb R^n$ of the relaxation (defined for every real $\varepsilon$).
--
--   These are the objects compared by Proposition 4.1 of the paper: a polyhedral approximation of the Lorentz cones turns (CQP) into a linear program whose feasible set lies between these two sets.
--
--   **Formalization Note** Vectors of $\mathbb R^n$ are functions `Fin n → ℝ`; the conic constraints are indexed by `Fin m` (0-based) and the matrices form a dependent family `(ℓ : Fin m) → Matrix (Fin (k ℓ)) (Fin n) ℝ`. The Euclidean norm is written out as `eucNorm y = √(∑ i, y i ^ 2)`, because the norm Mathlib puts on `Fin k → ℝ` is the sup norm. Only the feasible sets are used by the theorems; the objective $e$ is kept as part of the data.
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), p. 193 (PDF 1), display (CQP) and the Euclidean norm; p. 194 (PDF 2), display (CQP_ε)

import Mathlib

open Matrix

namespace PolyhedralSOC.Sandwich

/-- The Euclidean norm `‖y‖₂ = √(yᵀy)` of a vector `y ∈ ℝ^k`
(Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), p. 193 (PDF p. 1)). Written out explicitly
because the norm Mathlib puts on `Fin k → ℝ` is the sup norm. -/
noncomputable def eucNorm {k : ℕ} (y : Fin k → ℝ) : ℝ :=
  Real.sqrt (∑ i, y i ^ 2)

/-- The data of a conic quadratic problem
`(CQP)  min_x {eᵀx | Ax ≥ b, ‖A_ℓ x − b_ℓ‖₂ ≤ c_ℓᵀx − d_ℓ, ℓ = 1, …, m}`
(Ben-Tal & Nemirovski 2001, p. 193 (PDF p. 1)) with `x ∈ ℝ^n`, `A` a `k₀ × n` matrix,
`b ∈ ℝ^{k₀}`, and for each of the `m` conic constraints (indexed by `Fin m`, 0-based)
a `k_ℓ × n` matrix `A_ℓ`, `b_ℓ ∈ ℝ^{k_ℓ}`, `c_ℓ ∈ ℝ^n`, `d_ℓ ∈ ℝ`. The row sizes `k_ℓ`
may differ from constraint to constraint. -/
structure CQP (n k₀ m : ℕ) where
  /-- objective vector `e` -/
  e : Fin n → ℝ
  /-- the `k₀ × n` matrix `A` of the linear constraints `Ax ≥ b` -/
  A : Matrix (Fin k₀) (Fin n) ℝ
  /-- the right-hand side `b` of the linear constraints -/
  b : Fin k₀ → ℝ
  /-- the row size `k_ℓ` of `A_ℓ` -/
  k : Fin m → ℕ
  /-- the `k_ℓ × n` matrix `A_ℓ` of the `ℓ`-th conic constraint -/
  Aℓ : (ℓ : Fin m) → Matrix (Fin (k ℓ)) (Fin n) ℝ
  /-- the vector `b_ℓ ∈ ℝ^{k_ℓ}` of the `ℓ`-th conic constraint -/
  bℓ : (ℓ : Fin m) → Fin (k ℓ) → ℝ
  /-- the vector `c_ℓ ∈ ℝ^n` of the `ℓ`-th conic constraint -/
  c : Fin m → Fin n → ℝ
  /-- the scalar `d_ℓ` of the `ℓ`-th conic constraint -/
  d : Fin m → ℝ

/-- `Feas(CQP)`: the feasible set of (CQP) (Ben-Tal & Nemirovski 2001, p. 193 (PDF p. 1)),
the points `x` with `Ax ≥ b` (componentwise) and `‖A_ℓ x − b_ℓ‖₂ ≤ c_ℓᵀx − d_ℓ` for
every `ℓ`. -/
def feas {n k₀ m : ℕ} (P : CQP n k₀ m) : Set (Fin n → ℝ) :=
  {x | (∀ i, P.b i ≤ (P.A *ᵥ x) i) ∧
    ∀ ℓ, eucNorm (P.Aℓ ℓ *ᵥ x - P.bℓ ℓ) ≤ P.c ℓ ⬝ᵥ x - P.d ℓ}

/-- `Feas(CQP_ε)`: the feasible set of the `ε`-relaxation
`(CQP_ε)  min_x {eᵀx | Ax ≥ b, ‖A_ℓ x − b_ℓ‖₂ ≤ (1+ε)[c_ℓᵀx − d_ℓ], ℓ = 1, …, m}`
(Ben-Tal & Nemirovski 2001, p. 194 (PDF p. 2)). -/
def feasRelaxed {n k₀ m : ℕ} (P : CQP n k₀ m) (ε : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, P.b i ≤ (P.A *ᵥ x) i) ∧
    ∀ ℓ, eucNorm (P.Aℓ ℓ *ᵥ x - P.bℓ ℓ) ≤ (1 + ε) * (P.c ℓ ⬝ᵥ x - P.d ℓ)}

end PolyhedralSOC.Sandwich


