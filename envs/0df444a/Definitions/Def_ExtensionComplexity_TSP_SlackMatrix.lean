-- Prove2me | Definitions.Def_ExtensionComplexity_TSP_SlackMatrix
-- name    : ExtensionComplexity_TSP_SlackMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:47:28.878732+00:00
-- url     : https://prove2.me/theorems/3a07f2c0-88bc-431a-a1d8-dd860d9c7885
-- title:
--   Slack matrix, nonnegative rank $\mathrm{rank}_+$ and 1-monochromatic rectangle covers
-- statement:
--   1. **Slack matrix.** Let $P=\{x\in\mathbb R^{\iota} : Ax\le b\}=\mathrm{conv}(V)$ with $A\in\mathbb R^{m\times\iota}$, $b\in\mathbb R^m$ and $V=\{v_1,\dots,v_N\}$. The slack matrix of $P$ with respect to $Ax\le b$ and $V$ is the $m\times N$ matrix
--   $$S_{ij}:=b_i-A_iv_j,\qquad i\in[m],\ j\in[N],$$
--   where $A_i$ is the $i$-th row of $A$.
--   2. **Nonnegative rank.** A rank-$r$ nonnegative factorization of a matrix $M$ is a factorization $M=TU$ with $T$, $U$ entrywise nonnegative, $T$ having $r$ columns and $U$ having $r$ rows. The nonnegative rank $\mathrm{rank}_+(M)$ is the least such $r$.
--   3. **Rectangle covers.** For a $0/1$ matrix given by its set of $1$-entries, a rectangle is a Cartesian product $R_1\times R_2$ of a set of row indices and a set of column indices. A **1-monochromatic rectangle cover** of size $k$ is a family of $k$ rectangles, possibly overlapping, each containing only $1$-entries, that together contain every $1$-entry.
--
--   These three objects link geometry to combinatorics: Yannakakis's theorem (Theorem 3) identifies extension complexity with the nonnegative rank of a slack matrix, and Theorem 4 bounds the nonnegative rank below by the size of the smallest rectangle cover of the support.
--
--   **Formalization Note** The slack matrix is taken with respect to the given system and point list, with no restriction to facets or vertices, as in the paper. `nonnegRank M` is `sInf` of the set of admissible $r$, a natural number; for a nonnegative matrix with finitely many columns the set is nonempty ($M=M\cdot I$). The 0/1 matrix of a cover is passed as the predicate `f a b` "entry $(a,b)$ is $1$".
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, p. 17:9 (slack matrix; §3.1 nonnegative factorization and rank_+); p. 17:8, §2 (rectangle); p. 17:4, footnote 2 (rectangle covering bound)

import Mathlib

namespace ExtensionComplexity.TSP

open Matrix

/-- **Slack matrix** (p. 17:9): for `P = {x ∈ ℝ^ι | Ax ≤ b} = conv(V)` with `A ∈ ℝ^{m×ι}`,
`b ∈ ℝ^m` and points `V = {v_1, …, v_N}`, the slack matrix of `P` with respect to `Ax ≤ b` and `V`
is `S_ij := b_i − A_i v_j`, with rows indexed by the inequalities and columns by the points. -/
def slackMatrix {ι : Type*} [Fintype ι] {m N : ℕ} (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ)
    (V : Fin N → ι → ℝ) : Matrix (Fin m) (Fin N) ℝ :=
  fun i j => b i - (A *ᵥ V j) i

/-- A **rank-`r` nonnegative factorization** of `M` (p. 17:9, §3.1): `M = T U` with `T` and `U`
entrywise nonnegative, `T` with `r` columns and `U` with `r` rows. -/
def HasNonnegFactorization {α β : Type*} (M : Matrix α β ℝ) (r : ℕ) : Prop :=
  ∃ (T : Matrix α (Fin r) ℝ) (U : Matrix (Fin r) β ℝ),
    (∀ i l, 0 ≤ T i l) ∧ (∀ l j, 0 ≤ U l j) ∧ M = T * U

/-- **Nonnegative rank** `rank₊(M)` (p. 17:9, §3.1): the minimum rank among all nonnegative
factorizations of `M`. For a nonnegative matrix with finitely many columns the set is nonempty
(`M = M · I`); `sInf ∅ = 0` is never used. -/
noncomputable def nonnegRank {α β : Type*} (M : Matrix α β ℝ) : ℕ :=
  sInf {r : ℕ | HasNonnegFactorization M r}

/-- A **1-monochromatic rectangle cover** of the 0/1 matrix with 1-entries `{(a, b) | f a b}`
(p. 17:8, §2, and footnote 2, p. 17:4): `k` rectangles `R l = (rows, columns)`, each a Cartesian
product of a set of row indices and a set of column indices, such that every rectangle contains only
1-entries and every 1-entry lies in some rectangle. Rectangles may overlap; their number is `k`. -/
def IsOneRectangleCover {α β : Type*} (f : α → β → Prop) {k : ℕ}
    (R : Fin k → Set α × Set β) : Prop :=
  (∀ l, ∀ a ∈ (R l).1, ∀ b ∈ (R l).2, f a b) ∧
    (∀ a b, f a b → ∃ l, a ∈ (R l).1 ∧ b ∈ (R l).2)

end ExtensionComplexity.TSP


