-- Prove2me | Definitions.Def_MatousekLP_Simplex_Tableau
-- name    : MatousekLP_Simplex_Tableau
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T20:46:34.729762+00:00
-- url     : https://prove2.me/theorems/40dfe7b2-edfb-4713-8d88-51b19c26f4be
-- title:
--   Feasible bases, simplex tableaus, pivot steps and Bland's rule
-- statement:
--   This module fixes the vocabulary of Chapter 5 of Matoušek & Gärtner for a linear program in **equational form**
--
--   $$\text{maximize } c^{T}x \quad \text{subject to } Ax = b,\ x \ge 0,$$
--
--   where $A$ is a real $m\times n$ matrix, $b\in\mathbb{R}^m$ and $c\in\mathbb{R}^n$.
--
--   1. A **feasible solution** is an $x\in\mathbb{R}^n$ with $Ax=b$, $x\ge 0$; an **optimal solution** is a feasible $x$ with $c^Ty\le c^Tx$ for all feasible $y$; the program is **unbounded** if for every real $M$ some feasible $x$ has $c^Tx>M$. For a set $B$ of indices, the **basic solution determined by $B$** is an $x$ with $Ax=b$ and $x_j=0$ for all $j\notin B$.
--   2. For an $m$-element set $B=\{k_1<k_2<\dots<k_m\}\subseteq\{1,\dots,n\}$ write $N=\{1,\dots,n\}\setminus B=\{\ell_1<\dots<\ell_{n-m}\}$, and let $A_B$ ($m\times m$) and $A_N$ ($m\times(n-m)$) be the matrices of the columns of $A$ indexed by $B$ and by $N$, in increasing order. $B$ is a **feasible basis** if $A_B$ is nonsingular and $A_B^{-1}b\ge 0$.
--   3. A **simplex tableau** $T(B)$ is a system
--   $$x_B = p + Q\,x_N,\qquad z = z_0 + r^T x_N$$
--   with $p\in\mathbb{R}^m$, $Q\in\mathbb{R}^{m\times(n-m)}$, $z_0\in\mathbb{R}$, $r\in\mathbb{R}^{n-m}$, that has the same set of solutions $(x,z)$ as the system $Ax=b$, $z=c^Tx$. The module also defines the explicit parameters
--   $$Q=-A_B^{-1}A_N,\quad p=A_B^{-1}b,\quad z_0=c_B^TA_B^{-1}b,\quad r=c_N-(c_B^TA_B^{-1}A_N)^T.$$
--   4. In $T(B)$ (with these parameters), the nonbasic variable $x_v$, $v=\ell_\beta$, may **enter** and the basic variable $x_u$, $u=k_\alpha$, may **leave** if $r_\beta>0$, $q_{\alpha\beta}<0$ and
--   $$-\frac{p_\alpha}{q_{\alpha\beta}}=\min\Bigl\{-\frac{p_i}{q_{i\beta}} : q_{i\beta}<0,\ i=1,\dots,m\Bigr\}.$$
--   The new basis is $B'=(B\setminus\{u\})\cup\{v\}$.
--   5. A **pivot step** $B\to B'$ goes from a feasible basis $B$ to $B'$ by such an entering and leaving pair. A **Bland step** is a pivot step in which the entering variable is the one with the smallest index among all nonbasic variables with a positive coefficient in the last row, and the leaving variable is the one with the smallest index among all basic variables satisfying the leaving criterion for that entering variable.
--
--   These are the objects in which the simplex method and the theorem that Bland's rule prevents cycling are stated.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ`, so the book's indices $1,\dots,n$ become $0,\dots,n-1$; the tableau rows are indexed by `Fin m` (row $i$ belongs to $x_{k_i}$) and the nonbasic columns by `Fin (n - m)`. The sorted enumerations $k$ and $\ell$ are `Finset.orderEmbOfFin`, and every object that depends on them takes the proof `hB : B.card = m`. Nonsingularity of $A_B$ is `IsUnit (det A_B)`, so the Mathlib inverse `⁻¹` is the true inverse wherever it is used. "Smallest index" compares the variable indices $\ell_j$, $k_i$, as in the book, not row positions. The rank assumption of §4.2 is not part of these definitions; it is a hypothesis of every theorem.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 65 (§5.5, simplex tableau; feasible basis recalled), p. 66 (Lemma 5.5.1, formulas), pp. 67–68 (§5.6, entering and leaving variables, rule (5.3)), p. 72 (§5.7, Bland's rule); p. 3 (optimal solution), p. 41 (equational form)

import Mathlib
import Definitions.Def_MatousekLP_BFS_EquationalForm

namespace MatousekLP.Simplex

/-!
# Feasible bases, simplex tableaus, pivot steps and Bland's rule

Matoušek & Gärtner, *Understanding and Using Linear Programming*, Springer 2007, Chapter 5:
§5.5 (p. 65) simplex tableau, Lemma 5.5.1 (p. 66) its formulas, §5.6 (pp. 67–68) entering and
leaving variables and rule (5.3), §5.7 (p. 72) Bland's rule.

The linear program is `maximize cᵀx subject to Ax = b, x ≥ 0` (equational form) with
`A : Matrix (Fin m) (Fin n) ℝ`, `b : Fin m → ℝ`, `c : Fin n → ℝ`.
The book's indices `1, …, n` are `0, …, n-1` here.

For an `m`-element set `B ⊆ {0, …, n-1}` we write, as the book does on p. 67,
`B = {k₁ < ⋯ < k_m}` (`kIdx B hB`) and `N = {0, …, n-1} \ B = {ℓ₁ < ⋯ < ℓ_{n-m}}` (`lIdx B hB`).
The rows of a simplex tableau are indexed by `Fin m` (row `i` has the basic variable `x_{k_i}` on
the left) and its nonbasic columns by `Fin (n - m)` (column `j` belongs to `x_{ℓ_j}`).
-/

open Matrix

variable {m n : ℕ}

/-! ### The linear program -/

/-- The linear program is unbounded: the objective takes arbitrarily large values on feasible
solutions (p. 4). -/
def IsUnbounded (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) : Prop :=
  ∀ M : ℝ, ∃ x, MatousekLP.BFS.IsFeasible A b x ∧ M < c ⬝ᵥ x

/-- `x` is the basic solution determined by the index set `B`: `Ax = b` and `x_j = 0` for all
`j ∉ B`. For a basis `B` (with `A_B` nonsingular) there is exactly one such `x`
(Proposition 4.2.2); for a feasible basis it is the basic feasible solution of `B` (p. 66). -/
def IsBasicSolutionFor (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (B : Finset (Fin n))
    (x : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ ∀ j, j ∉ B → x j = 0

/-! ### Bases in sorted order -/

/-- `|N| = n - m` when `|B| = m`, for `N = {0, …, n-1} \ B`. -/
theorem card_compl_eq {B : Finset (Fin n)} (hB : B.card = m) : Bᶜ.card = n - m := by
  rw [Finset.card_compl, Fintype.card_fin, hB]

/-- `k₁ < k₂ < ⋯ < k_m`: the elements of `B` in increasing order (p. 67). -/
noncomputable def kIdx (B : Finset (Fin n)) (hB : B.card = m) : Fin m → Fin n :=
  B.orderEmbOfFin hB

/-- `ℓ₁ < ℓ₂ < ⋯ < ℓ_{n-m}`: the elements of `N = {0, …, n-1} \ B` in increasing order
(p. 67). -/
noncomputable def lIdx (B : Finset (Fin n)) (hB : B.card = m) : Fin (n - m) → Fin n :=
  Bᶜ.orderEmbOfFin (card_compl_eq hB)

/-- `A_B`: the `m × m` matrix of the columns of `A` indexed by `B`, in the order `k₁, …, k_m`. -/
noncomputable def basisMatrix (A : Matrix (Fin m) (Fin n) ℝ) (B : Finset (Fin n)) (hB : B.card = m) :
    Matrix (Fin m) (Fin m) ℝ :=
  A.submatrix id (kIdx B hB)

/-- `A_N`: the `m × (n-m)` matrix of the columns of `A` indexed by `N`, in the order
`ℓ₁, …, ℓ_{n-m}`. -/
noncomputable def nonbasisMatrix (A : Matrix (Fin m) (Fin n) ℝ) (B : Finset (Fin n)) (hB : B.card = m) :
    Matrix (Fin m) (Fin (n - m)) ℝ :=
  A.submatrix id (lIdx B hB)

/-- `B` (with `|B| = m`, witnessed by `hB`) is a **feasible basis** (pp. 46, 65): `A_B` is
nonsingular and the unique solution `A_B⁻¹ b` of `A_B x_B = b` is nonnegative. -/
def IsFeasibleBasisOf (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (B : Finset (Fin n))
    (hB : B.card = m) : Prop :=
  IsUnit (basisMatrix A B hB).det ∧ 0 ≤ (basisMatrix A B hB)⁻¹ *ᵥ b

/-- `B` is a **feasible basis**: an `m`-element set `B ⊆ {0, …, n-1}` with `A_B` nonsingular and
`A_B⁻¹ b ≥ 0` (pp. 46, 65). -/
def IsFeasibleBasis (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (B : Finset (Fin n)) :
    Prop :=
  ∃ hB : B.card = m, IsFeasibleBasisOf A b B hB

/-! ### The simplex tableau `T(B)` -/

/-- A **simplex tableau** for the `m`-element set `B` (§5.5, p. 65): the system
`x_B = p + Q x_N`, `z = z₀ + rᵀ x_N` in the variables `x₁, …, x_n, z` has the same set of
solutions as `Ax = b, z = cᵀx`. Here `x_B = (x_{k₁}, …, x_{k_m})` and
`x_N = (x_{ℓ₁}, …, x_{ℓ_{n-m}})`. -/
def IsSimplexTableau (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (B : Finset (Fin n)) (hB : B.card = m) (p : Fin m → ℝ) (Q : Matrix (Fin m) (Fin (n - m)) ℝ)
    (z₀ : ℝ) (r : Fin (n - m) → ℝ) : Prop :=
  ∀ (x : Fin n → ℝ) (z : ℝ),
    (A *ᵥ x = b ∧ z = c ⬝ᵥ x) ↔
      ((fun i => x (kIdx B hB i)) = p + Q *ᵥ (fun j => x (lIdx B hB j)) ∧
        z = z₀ + r ⬝ᵥ (fun j => x (lIdx B hB j)))

/-- `p = A_B⁻¹ b` (Lemma 5.5.1). -/
noncomputable def tableauP (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (B : Finset (Fin n))
    (hB : B.card = m) : Fin m → ℝ :=
  (basisMatrix A B hB)⁻¹ *ᵥ b

/-- `Q = −A_B⁻¹ A_N` (Lemma 5.5.1). -/
noncomputable def tableauQ (A : Matrix (Fin m) (Fin n) ℝ) (B : Finset (Fin n))
    (hB : B.card = m) : Matrix (Fin m) (Fin (n - m)) ℝ :=
  -((basisMatrix A B hB)⁻¹ * nonbasisMatrix A B hB)

/-- `z₀ = c_Bᵀ A_B⁻¹ b` (Lemma 5.5.1), with `c_B = (c_{k₁}, …, c_{k_m})`. -/
noncomputable def tableauZ0 (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (B : Finset (Fin n)) (hB : B.card = m) : ℝ :=
  (fun i => c (kIdx B hB i)) ⬝ᵥ ((basisMatrix A B hB)⁻¹ *ᵥ b)

/-- `r = c_N − (c_Bᵀ A_B⁻¹ A_N)ᵀ` (Lemma 5.5.1), with `c_N = (c_{ℓ₁}, …, c_{ℓ_{n-m}})`. -/
noncomputable def tableauR (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (B : Finset (Fin n))
    (hB : B.card = m) : Fin (n - m) → ℝ :=
  (fun j => c (lIdx B hB j)) -
    (fun i => c (kIdx B hB i)) ᵥ* ((basisMatrix A B hB)⁻¹ * nonbasisMatrix A B hB)

/-! ### Pivot steps -/

/-- The entering variable `x_v`, `v = ℓ_β`, and the leaving variable `x_u`, `u = k_α`, satisfy
the criteria of §5.6 (pp. 67–68) in the tableau `T(B)` (with the parameters of Lemma 5.5.1):
the coefficient `r_β` of `x_v` in the last row is positive, and rule (5.3) holds:
`q_{αβ} < 0` and `−p_α/q_{αβ} = min {−p_i/q_{iβ} : q_{iβ} < 0}`. -/
def IsEnteringLeaving (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (B : Finset (Fin n)) (hB : B.card = m) (β : Fin (n - m)) (α : Fin m) : Prop :=
  0 < tableauR A c B hB β ∧ tableauQ A B hB α β < 0 ∧
    ∀ i, tableauQ A B hB i β < 0 →
      -tableauP A b B hB α / tableauQ A B hB α β ≤ -tableauP A b B hB i / tableauQ A B hB i β

/-- The new basis `B′ = (B \ {u}) ∪ {v}` with `u = k_α` leaving and `v = ℓ_β` entering (p. 67). -/
noncomputable def pivotBasis (B : Finset (Fin n)) (hB : B.card = m) (β : Fin (n - m))
    (α : Fin m) : Finset (Fin n) :=
  insert (lIdx B hB β) (B.erase (kIdx B hB α))

/-- One pivot step of the simplex method with an arbitrary pivot rule (§5.6): `B` is a feasible
basis, some entering variable `x_{ℓ_β}` and leaving variable `x_{k_α}` satisfy the criteria of
§5.6, and `B′ = (B \ {k_α}) ∪ {ℓ_β}`. -/
def SimplexStep (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (B B' : Finset (Fin n)) : Prop :=
  ∃ hB : B.card = m, IsFeasibleBasisOf A b B hB ∧
    ∃ (β : Fin (n - m)) (α : Fin m),
      IsEnteringLeaving A b c B hB β α ∧ B' = pivotBasis B hB β α

/-- One pivot step of the simplex method with **Bland's rule** (§5.7, p. 72): the entering
variable is the improving variable (positive coefficient in the last row) with the smallest
index, and the leaving variable is, among all variables satisfying (5.3) for that entering
variable, the one with the smallest index. Indices are variable indices `ℓ_j`, `k_i`. -/
def BlandStep (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (B B' : Finset (Fin n)) : Prop :=
  ∃ hB : B.card = m, IsFeasibleBasisOf A b B hB ∧
    ∃ (β : Fin (n - m)) (α : Fin m),
      IsEnteringLeaving A b c B hB β α ∧
      (∀ j, 0 < tableauR A c B hB j → lIdx B hB β ≤ lIdx B hB j) ∧
      (∀ i, IsEnteringLeaving A b c B hB β i → kIdx B hB α ≤ kIdx B hB i) ∧
      B' = pivotBasis B hB β α

end MatousekLP.Simplex


