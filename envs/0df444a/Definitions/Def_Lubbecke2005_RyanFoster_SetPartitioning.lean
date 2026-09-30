-- Prove2me | Definitions.Def_Lubbecke2005_RyanFoster_SetPartitioning
-- name    : Lubbecke2005_RyanFoster_SetPartitioning
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T15:31:46.401149+00:00
-- url     : https://prove2.me/theorems/16084a4d-5114-49f1-b00b-75f123e94221
-- title:
--   Set-partitioning data: $0/1$ matrices, $0/1$ vectors and the Ryan–Foster quantity $\sum_{j} a_{rj}a_{sj}\lambda_j$
-- statement:
--   Let $m, n \ge 0$ be integers. Rows are indexed by $\{1, \dots, m\}$ and columns by a finite set $J'$ with $|J'| = n$. A real $m \times n$ matrix $A = (a_{rj})$ is a **$0/1$ matrix**, written $A \in \{0,1\}^{m \times |J'|}$, when every entry $a_{rj}$ equals $0$ or $1$. Column $j$ **covers** row $r$ when $a_{rj} = 1$, so a column of a set-partitioning problem is the same thing as a subset of the rows.
--
--   A vector $\lambda \in \mathbb R^{J'}$ is a **$0/1$ vector**, $\lambda \in \{0,1\}^{|J'|}$, when every coordinate $\lambda_j$ equals $0$ or $1$. A solution of $A\lambda = \mathbf 1$, $\lambda \ge \mathbf 0$ that is not a $0/1$ vector is called **fractional**.
--
--   For rows $r, s$ and a vector $\lambda$, the **Ryan–Foster quantity** is
--
--   $$\sum_{j \in J'} a_{rj}\, a_{sj}\, \lambda_j ,$$
--
--   the total weight that $\lambda$ puts on the columns covering both $r$ and $s$.
--
--   These are the objects of Proposition 3 of Lübbecke and Desrosiers (2005) and of the Ryan–Foster branching rule built on it: one branch fixes the quantity of a pair of rows to $1$ (both rows covered by the same column), the other to $0$ (covered by two distinct columns).
--
--   **Formalization Note** Rows are `Fin m`, columns `Fin n` (so $J'$ is identified with $\{0, \dots, n-1\}$), and the matrix and the vector are real-valued, with the $0/1$ property stated as a predicate (`IsZeroOneMatrix`, `IsZeroOneVector`). The quantity is `pairCover A λ r s`; the Lean identifier for $\lambda$ is `lam`, since `λ` is a Lean keyword.
-- source:
--   Lübbecke and Desrosiers, Selected Topics in Column Generation, Operations Research 53(6), 2005, p. 1020, §7.3, Proposition 3 and the paragraph after it

import Mathlib

open Matrix

namespace Lubbecke2005.RyanFoster

/-- A matrix all of whose entries are `0` or `1`: the book's `A ∈ {0, 1}^{m×|J′|}`
(Lübbecke–Desrosiers 2005, §7.3, p. 1020, Proposition 3). Column `j` *covers* row `r`
when `A r j = 1`. -/
def IsZeroOneMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ r j, A r j = 0 ∨ A r j = 1

/-- A vector all of whose coordinates are `0` or `1`, i.e. `λ ∈ {0, 1}^{|J′|}`.
A solution `λ` of `Aλ = 𝟏, λ ⩾ 𝟎` is *fractional* when it is not such a vector
(§7.3, p. 1020, Proposition 3). -/
def IsZeroOneVector {n : ℕ} (lam : Fin n → ℝ) : Prop :=
  ∀ j, lam j = 0 ∨ lam j = 1

/-- The Ryan–Foster quantity of rows `r` and `s` at `λ`:
`∑_{j ∈ J′} a_rj a_sj λ_j`, the total weight of the columns that cover both rows
(§7.3, p. 1020). -/
def pairCover {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (lam : Fin n → ℝ)
    (r s : Fin m) : ℝ :=
  ∑ j, A r j * A s j * lam j

end Lubbecke2005.RyanFoster


