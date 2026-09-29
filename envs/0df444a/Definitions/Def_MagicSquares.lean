-- Prove2me | Definitions.Def_MagicSquares
-- name    : MagicSquares
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-09-16T12:09:43.984434+00:00
-- url     : https://prove2.me/theorems/be2f2b6a-a540-47ae-b487-ac22532a2745
-- title:
--   Magic squares: core definitions and counting functions
-- statement:
--   Core vocabulary for the theory of magic squares: an $n \times n$ array
--   (`Square`), its row, column, main-diagonal, anti-diagonal and broken-diagonal sums, and the
--   standard predicates used in the literature.
--
--   A **semi-magic square** of line sum $s$ has every row and every column summing to $s$; it is
--   **magic** if both main diagonals also sum to $s$, and **panmagic** (pandiagonal) if every
--   broken diagonal in both directions does. A square is **associative** with constant $c$ when
--   centrally opposite cells sum to $c$, and **compact** with constant $c$ when every
--   $2 \times 2$ block -- including the ones that wrap around the edges -- sums to $c$.
--
--   A square is **normal** of order $n$ when its entries are exactly the integers
--   $1, \dots, n^{2}$, each occurring once. Then `magicConstant n` $= n(n^{2}+1)/2$ is the common
--   line sum, and `complement` is the involution $M \mapsto n^{2}+1-M$.
--
--   Finally the module fixes the four classical counting functions: $H_{n}(t)$ (semi-magic),
--   $M_{n}(t)$ (magic), $P_{n}(t)$ (panmagic) and $S_{n}(t)$ (symmetric magic), each counting
--   squares of order $n$ with nonnegative integer entries and line sum $t$. Since every entry of
--   such a square is at most $t$, searching over arrays with entries in $\{0,\dots,t\}$ loses
--   nothing.
--
--   **Formalization Note** Entries are indexed by `Fin n`, so broken diagonals are obtained by
--   addition modulo $n$ and the anti-diagonal by `Fin.rev`. The counting functions are
--   cardinalities of finsets of arrays over `Fin (t+1)`.
-- source:
--   Beck, Cohen, Cuomo & Gribelyuk, The number of ``magic'' squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707-717; arXiv:math/0201013v3, Section 1 (definitions) and Section 2 (Theorem 1).

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

/-!
# Magic squares: core vocabulary

This module fixes the combinatorial vocabulary used throughout the magic-square
formalization. It contains only definitions (plus their immediate `simp`
companions); every substantive statement is submitted separately as a theorem.

Conventions follow Beck, Cohen, Cuomo and Gribelyuk, *The number of "magic"
squares, cubes and hypercubes*, Amer. Math. Monthly **110** (2003), 707--717
(arXiv:math/0201013) for the weak (nonnegative-integer) reading, and the
classical literature for the *normal* reading where the entries are exactly
`1, …, n²`.

An `n × n` array is `Square n α`, i.e. `Matrix (Fin n) (Fin n) α`. All sums are
taken over `Finset.univ`, and indices on broken diagonals are read modulo `n`.
-/

namespace MagicSquares

/-- An `n × n` array with entries in `α`. -/
abbrev Square (n : ℕ) (α : Type*) := Matrix (Fin n) (Fin n) α

variable {n : ℕ} {α : Type*}

/-! ## Line sums -/

/-- The sum of the entries in row `i`. -/
def rowSum [AddCommMonoid α] (M : Square n α) (i : Fin n) : α :=
  ∑ j, M i j

/-- The sum of the entries in column `j`. -/
def colSum [AddCommMonoid α] (M : Square n α) (j : Fin n) : α :=
  ∑ i, M i j

/-- The sum of the entries on the main (descending) diagonal. -/
def diagSum [AddCommMonoid α] (M : Square n α) : α :=
  ∑ i, M i i

/-- The sum of the entries on the anti-diagonal, i.e. the cells `(i, n-1-i)`. -/
def antiDiagSum [AddCommMonoid α] (M : Square n α) : α :=
  ∑ i, M i (Fin.rev i)

/-- The sum of the entries on the broken descending diagonal of offset `k`,
i.e. the cells `(i, i + k)` with the column index read modulo `n`.
For `k = 0` this is `diagSum`. -/
def brokenDiagSum [AddCommMonoid α] (M : Square n α) (k : Fin n) : α :=
  ∑ i, M i (i + k)

/-- The sum of the entries on the broken ascending diagonal of offset `k`,
i.e. the cells `(i, n - 1 - i + k)`.
For `k = 0` this is `antiDiagSum`. -/
def brokenAntiDiagSum [AddCommMonoid α] (M : Square n α) (k : Fin n) : α :=
  ∑ i, M i (Fin.rev i + k)

/-- The sum of all entries of the array. -/
def totalSum [AddCommMonoid α] (M : Square n α) : α :=
  ∑ i, ∑ j, M i j

/-! ## The magic predicates -/

/-- A **semi-magic square** of line sum `s`: every row and every column sums to
`s`. Entries are not required to be distinct. -/
def IsSemiMagic [AddCommMonoid α] (M : Square n α) (s : α) : Prop :=
  (∀ i, rowSum M i = s) ∧ (∀ j, colSum M j = s)

/-- A **magic square** of line sum `s`: semi-magic, and both main diagonals sum
to `s` as well. Entries are not required to be distinct. -/
def IsMagic [AddCommMonoid α] (M : Square n α) (s : α) : Prop :=
  IsSemiMagic M s ∧ diagSum M = s ∧ antiDiagSum M = s

/-- A **panmagic (pandiagonal) square** of line sum `s`: semi-magic, and *every*
broken diagonal in both directions sums to `s`. -/
def IsPanMagic [AddCommMonoid α] (M : Square n α) (s : α) : Prop :=
  IsSemiMagic M s ∧
    (∀ k, brokenDiagSum M k = s) ∧
      (∀ k, brokenAntiDiagSum M k = s)

/-- An **associative (regular) square** with complement constant `c`: every pair
of cells centrally opposite each other sums to `c`. -/
def IsAssociative [Add α] (M : Square n α) (c : α) : Prop :=
  ∀ i j, M i j + M (Fin.rev i) (Fin.rev j) = c

/-- A **compact square** with block constant `c`: every `2 × 2` block, including
those that wrap around the edges, sums to `c`. -/
def IsCompact [NeZero n] [AddCommMonoid α] (M : Square n α) (c : α) : Prop :=
  letI := Fin.instAddMonoidWithOne n
  ∀ i j : Fin n, M i j + M i (j + 1) + M (i + 1) j + M (i + 1) (j + 1) = c

/-- A **symmetric** square: `M` equals its transpose. -/
def IsSymmetric (M : Square n α) : Prop :=
  ∀ i j, M i j = M j i

/-- A **bimagic square**: `M` is magic with line sum `s`, and the array of
squared entries is magic with line sum `s₂`. -/
def IsBimagic (M : Square n ℕ) (s s₂ : ℕ) : Prop :=
  IsMagic M s ∧ IsMagic (fun i j => (M i j) ^ 2) s₂

/-! ## Normal squares -/

/-- A **normal** square of order `n`: the entries are exactly the integers
`1, 2, …, n²`, each occurring once.

Formally this is stated as (i) every entry lies in `Icc 1 (n^2)` and (ii) the
index-to-entry map is injective. Together these say the entries are a
permutation of `1, …, n²`. -/
def IsNormal (M : Square n ℕ) : Prop :=
  (∀ p : Fin n × Fin n, 1 ≤ M p.1 p.2 ∧ M p.1 p.2 ≤ n ^ 2) ∧
    Function.Injective (fun p : Fin n × Fin n => M p.1 p.2)

/-- The magic constant of a normal magic square of order `n`, namely
`n (n² + 1) / 2`. -/
def magicConstant (n : ℕ) : ℕ := n * (n ^ 2 + 1) / 2

/-- The complementary square of a normal square: `M ↦ n² + 1 - M`. -/
def complement (M : Square n ℕ) : Square n ℕ :=
  fun i j => n ^ 2 + 1 - M i j

/-! ## Counting functions

Every entry of a (semi-)magic square with nonnegative entries and line sum `t`
is at most `t`, so the finite search space `Square n (Fin (t+1))` is lossless. -/

noncomputable section

/-- All semi-magic squares of order `n` and line sum `t`. -/
def semiMagicSquares (n t : ℕ) : Finset (Square n (Fin (t + 1))) :=
  by classical exact Finset.univ.filter fun M => IsSemiMagic (fun i j => (M i j : ℕ)) t

/-- All magic squares of order `n` and line sum `t`. -/
def magicSquares (n t : ℕ) : Finset (Square n (Fin (t + 1))) :=
  by classical exact Finset.univ.filter fun M => IsMagic (fun i j => (M i j : ℕ)) t

/-- All panmagic squares of order `n` and line sum `t`. -/
def panMagicSquares (n t : ℕ) : Finset (Square n (Fin (t + 1))) :=
  by classical exact Finset.univ.filter fun M => IsPanMagic (fun i j => (M i j : ℕ)) t

/-- All symmetric magic squares of order `n` and line sum `t`. -/
def symmetricMagicSquares (n t : ℕ) : Finset (Square n (Fin (t + 1))) :=
  by classical exact (Finset.univ.filter (fun M : Square n (Fin (t + 1)) => IsMagic (fun i j => (M i j : ℕ)) t ∧ IsSymmetric (fun i j => (M i j : ℕ))))

/-- `H_n(t)`: the number of semi-magic squares of order `n` and line sum `t`. -/
def semiMagicCount (n t : ℕ) : ℕ := (semiMagicSquares n t).card

/-- `M_n(t)`: the number of magic squares of order `n` and line sum `t`. -/
def magicCount (n t : ℕ) : ℕ := (magicSquares n t).card

/-- `P_n(t)`: the number of panmagic squares of order `n` and line sum `t`. -/
def panMagicCount (n t : ℕ) : ℕ := (panMagicSquares n t).card

/-- `S_n(t)`: the number of symmetric magic squares of order `n` and line sum `t`. -/
def symmetricMagicCount (n t : ℕ) : ℕ := (symmetricMagicSquares n t).card

end

end MagicSquares


