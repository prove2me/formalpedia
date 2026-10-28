-- Prove2me | Definitions.Def_NQueensComp_NPC_Queens
-- name    : NQueensComp_NPC_Queens
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:45.293985+00:00
-- url     : https://prove2.me/theorems/fa24c78e-c787-4bcf-8265-cddbbcb20e97
-- title:
--   Queens, attacks, n-Queens solutions, modular solutions, and the sets Q₁₉, Aₙ, Bₙ (Definition 1, Problem 1, Definition 5)
-- statement:
--   This module sets up the chessboard objects of §2 and §4.1.
--
--   1. **Queens** (Definition 1). A queen is a pair $q=(\alpha,\beta)$ of integers with $\alpha,\beta\ge0$; $\mathrm{col}(q)=\alpha$, $\mathrm{row}(q)=\beta$, its sum-diagonal is $\alpha+\beta$ and its difference-diagonal is the integer $\alpha-\beta$. The size is $\|q\|=\max(\alpha,\beta)$, and $q$ fits on board size $n$ iff $\|q\|<n$.
--   2. **Attack.** $q$ attacks $q_1$ iff $q\ne q_1$ and $\alpha=\alpha_1$, or $\beta=\beta_1$, or $\alpha+\beta=\alpha_1+\beta_1$, or $\alpha-\beta=\alpha_1-\beta_1$.
--   3. **Arithmetic on queens.** $iq=(i\alpha,i\beta)$, $q+q_1=(\alpha+\alpha_1,\beta+\beta_1)$, $iQ=\{iq\mid q\in Q\}$, $Q+q_1=\{q+q_1\mid q\in Q\}$ and $Q+Q_1=\{q+q_1\mid q\in Q,\ q_1\in Q_1\}$.
--   4. **n-Queens** (Problem 1). For $n\ge1$, a solution is a set $Q$ of $n$ queens that all fit on board size $n$, no two of which attack each other. It is **modular** if moreover any two distinct queens have $\alpha_1+\beta_1\not\equiv\alpha_2+\beta_2$ and $\alpha_1-\beta_1\not\equiv\alpha_2-\beta_2 \pmod n$.
--   5. **The sets of Definition 5.**
--   $$Q_{19}=\{(0,8),(1,12),(2,17),(3,7),(4,10),(5,15),(6,1),(7,16),(8,13),(9,2),(10,6),(11,18),(12,3),(13,5),(14,11),(15,9),(16,14),(17,0),(18,4)\},$$
--   $$A_n=\{(i,2i\bmod n)\mid 0\le i<n\},\qquad B_n=\{(2i\bmod n,i)\mid 0\le i<n\}.$$
--
--   These are the building blocks of the reduction from Problem 3 to n-Queens Completion (Definition 10) and of every statement about boards in the mission.
--
--   **Formalization Note** A queen is `ℕ × ℕ` (column, row); the difference-diagonal is computed in `ℤ`, never with truncated subtraction. Sets of queens are `Finset (ℕ × ℕ)`. Scalars $i$ are natural numbers (`i • q`), which covers every use in the paper. Problem 1's requirement $n\ge1$ is part of `IsNQueensSol`.
-- source:
--   Gent, Jefferson & Nightingale, Complexity of n-Queens Completion, J. Artif. Intell. Res. 59 (2017), p. 818, Definition 1 and Problem 1; p. 822, Definition 5

import Mathlib

namespace NQueensComp.NPC

/-- A queen `q = (α, β)` with `0 ≤ α, 0 ≤ β` (Definition 1): `α` is its column, `β` its row. -/
abbrev Queen := ℕ × ℕ

/-- The column `col(q) = α` of `q = (α, β)`. -/
def col (q : Queen) : ℕ := q.1

/-- The row `row(q) = β` of `q = (α, β)`. -/
def row (q : Queen) : ℕ := q.2

/-- The sum-diagonal `α + β` of `q = (α, β)`. -/
def sumDiag (q : Queen) : ℕ := q.1 + q.2

/-- The difference-diagonal `α − β` of `q = (α, β)`, an integer (no truncated subtraction). -/
def diffDiag (q : Queen) : ℤ := (q.1 : ℤ) - (q.2 : ℤ)

/-- The size `‖q‖ = max(α, β)`. -/
def size (q : Queen) : ℕ := max q.1 q.2

/-- `q` fits on board size `n`: `‖q‖ < n`. -/
def FitsOn (n : ℕ) (q : Queen) : Prop := size q < n

/-- `q` attacks `q₁`: `q ≠ q₁` and they share a column, a row, a sum-diagonal or a
difference-diagonal (Definition 1). -/
def Attacks (q q₁ : Queen) : Prop :=
  q ≠ q₁ ∧ (col q = col q₁ ∨ row q = row q₁ ∨ sumDiag q = sumDiag q₁ ∨ diffDiag q = diffDiag q₁)

/-- No queen of `Q` attacks another queen of `Q`. -/
def NonAttacking (Q : Finset Queen) : Prop :=
  ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, ¬ Attacks q₁ q₂

/-- `Q + q₁ = {q + q₁ | q ∈ Q}` (Definition 1); `+` on `ℕ × ℕ` is componentwise. -/
def shiftSet (Q : Finset Queen) (q₁ : Queen) : Finset Queen :=
  Q.image (fun q => q + q₁)

/-- `iQ = {iq | q ∈ Q}` with `iq = (iα, iβ)` (Definition 1). -/
def scaleSet (i : ℕ) (Q : Finset Queen) : Finset Queen :=
  Q.image (fun q => i • q)

/-- `Q + Q₁ = {q + q₁ | q ∈ Q, q₁ ∈ Q₁}` (Definition 1). -/
def sumSet (Q Q₁ : Finset Queen) : Finset Queen :=
  (Q ×ˢ Q₁).image (fun p => p.1 + p.2)

/-- `Q` is a solution to the `n`-Queens problem (Problem 1): `n ≥ 1`, every queen of `Q` fits on
board size `n`, `|Q| = n`, and no two distinct queens of `Q` attack each other. -/
def IsNQueensSol (n : ℕ) (Q : Finset Queen) : Prop :=
  1 ≤ n ∧ (∀ q ∈ Q, FitsOn n q) ∧ Q.card = n ∧ NonAttacking Q

/-- `Q` is a modular solution to the `n`-Queens problem (Problem 1): a solution such that any two
distinct queens have sum-diagonals and difference-diagonals that differ modulo `n`. -/
def IsModularSol (n : ℕ) (Q : Finset Queen) : Prop :=
  IsNQueensSol n Q ∧
    ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, q₁ ≠ q₂ →
      ¬ ((sumDiag q₁ : ℤ) ≡ (sumDiag q₂ : ℤ) [ZMOD (n : ℤ)]) ∧
        ¬ (diffDiag q₁ ≡ diffDiag q₂ [ZMOD (n : ℤ)])

/-- The 19-queens solution `Q₁₉` of Definition 5 (p. 822). -/
def Q19 : Finset Queen :=
  {(0, 8), (1, 12), (2, 17), (3, 7), (4, 10), (5, 15), (6, 1), (7, 16), (8, 13), (9, 2),
   (10, 6), (11, 18), (12, 3), (13, 5), (14, 11), (15, 9), (16, 14), (17, 0), (18, 4)}

/-- `Aₙ = {(i, 2i mod n) | 0 ≤ i < n}` (Definition 5). -/
def A (n : ℕ) : Finset Queen :=
  (Finset.range n).image (fun i => (i, 2 * i % n))

/-- `Bₙ = {(2i mod n, i) | 0 ≤ i < n}` (Definition 5). -/
def B (n : ℕ) : Finset Queen :=
  (Finset.range n).image (fun i => (2 * i % n, i))

end NQueensComp.NPC


