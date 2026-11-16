-- Prove2me | Definitions.Def_PatternRangeCounting1593_RangeCounting_Supplement_MatrixAccess
-- name    : PatternRangeCounting1593_RangeCounting_Supplement_MatrixAccess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:04:05.168197+00:00
-- url     : https://prove2.me/theorems/57a20806-b88e-4010-b275-2764c0bcc1a1
-- title:
--   XOR difference array, rank permutation $\sigma_P$, board pattern $\rho_k$, matrix input layouts and representations
-- statement:
--   This file fixes the objects of the matrix-access part of the paper (§§1.2, 2.2, 6 and 7.2). A binary $r\times c$ matrix $M$ has entries in $\{0,1\}$; the paper's rows and columns are 1-based, $(i,j)\in[r]\times[c]$.
--
--   1. **Zero padding and XOR difference array** (Equation (2)). Put $M[0,\cdot]=M[\cdot,0]=0$. The two-dimensional XOR difference array $D$ has the same dimensions as $M$ and
--   $$D[i,j]=M[i,j]\oplus M[i-1,j]\oplus M[i,j-1]\oplus M[i-1,j-1]\qquad((i,j)\in[r]\times[c]).$$
--   Its support $\operatorname{supp}(D)$ is the set of positions with $D[i,j]=1$.
--
--   2. **Rank permutation** (§6.1). For a set $P\subseteq[r]\times[c]$ of $m$ cells (several cells may share a row or a column), list $P$ in row-major order (by row, then by column) and in column-major order (by column, then by row). The rank permutation $\sigma_P\in S_m$ sends the position of a cell in the first list to its position in the second list. The 0/1 indicator matrix of $P$ is the matrix with ones exactly on $P$.
--
--   3. **Board pattern** (Equation (13)). For $k\ge1$, $\rho_k\in S_{k^2}$ maps the row-major rank of each square of the $k\times k$ board to its column-major rank: $\rho_k((p-1)k+q)=(q-1)k+p$ for $p,q\in[k]$.
--
--   4. **Counts.** For cutoffs $0\le i\le r$, $0\le j\le c$, the dominance count is $|P\cap([i]\times[j])|$ with $[0]=\emptyset$; for endpoints $i_1,i_2\le r$, $j_1,j_2\le c$ the rectangle count is $|P\cap([i_1,i_2]\times[j_1,j_2])|$, zero for an empty interval.
--
--   5. **Constructor inputs.** An explicit list of cells is stored with the 1-based row and column of the $a$-th listed cell in memory words $2a$ and $2a+1$; a list "enumerates" $P$ if it contains every cell of $P$ exactly once and nothing else, in any order. A list of rectangles $[a,b]\times[p,q]$ is stored with $a,b,p,q$ of the $u$-th rectangle in words $4u,\dots,4u+3$. An *exact disjoint cover* of $M$ is a list of rectangles with $1\le a\le b\le r$, $1\le p\le q\le c$, any two of which share no cell, whose union is exactly the set of one-entries of $M$.
--
--   6. **Representations.** A packed bit string $\mathrm{bits}$ (stored in $w$-bit words) is an *entry-access representation* of $M$ for a query program $Q$ and step bounds $T_0$, $T$, threshold $n_0$ if, for every $(i,j)\in[r]\times[c]$, $Q$ started on that memory with registers $(r,c,|\mathrm{bits}|,i,j)$ halts within $T_0$ steps with $M[i,j]$ in register $0$, and within $T$ steps when $r+c\ge n_0$. A *counting representation* of $P$ is the same for a dominance program (registers $(r,c,|\mathrm{bits}|,i,j)$, output the dominance count) and a rectangle program (registers $(r,c,|\mathrm{bits}|,i_1,i_2,j_1,j_2)$, output the rectangle count).
--
--   Mixed-freeness, twin orders and grid minors are the published definitions of the Twin-width I series; the word RAM, packing, runs and construction runs are the published definitions of the live mission.
--
--   **Formalization Note** Matrix indices are 0-based (`Fin r`, `Fin c`): index $a$ is the paper's row $a+1$. Orders are lexicographic orders on `(row, column)` and `(column, row)`; positions of $\sigma_P$ and $\rho_k$ are 0-based (`Fin m`), so $\rho_k(pk+q)=qk+p$ for $p,q<k$.
-- source:
--   Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), Equation (2), printed p. 7 (PDF p. 8); §6.1 and Equation (13), printed p. 21 (PDF p. 22); Theorem 1.2, printed p. 2 (PDF p. 3); Corollary 7.2, printed p. 25 (PDF p. 26)

import Mathlib
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Perm
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Machine
import Definitions.Def_TwinWidthI_GridThm_Setting

set_option autoImplicit false

namespace PatternRangeCounting1593.RangeCounting.Supplement

open PatternRangeCounting1593.RangeCounting

/-!
# Matrix access through counting: the objects of §§2.2, 6 and 7.2

Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), Equation (2), printed p. 7
(PDF p. 8); §6.1, printed p. 21 (PDF p. 22); Theorem 1.2, printed p. 2 (PDF p. 3);
Corollary 7.2, printed p. 25 (PDF p. 26).

A binary `r × c` matrix is a `Matrix (Fin r) (Fin c) Bool` (`true` = 1). The paper's row `i`
and column `j` (1-based, `[r] × [c]`) are the indices `i - 1 : Fin r` and `j - 1 : Fin c`.
Mixed-freeness, twin orders and grid minors are the published definitions
`TwinWidthI.GridThm.MixedFree`, `TwinWidthI.GridThm.TwinOrdered` and
`TwinWidthI.GridThm.HasGridMinor`.
-/

section Matrices

variable {r c : ℕ}

/-- The matrix `M` padded with a zero row `0` and a zero column `0`, read with the paper's
1-based coordinates: `padded M i j = M[i, j]` for `(i, j) ∈ [r] × [c]` and `0` (`false`)
otherwise, in particular in row `0` and column `0`. -/
def padded (M : Matrix (Fin r) (Fin c) Bool) (i j : ℕ) : Bool :=
  if h : 1 ≤ i ∧ i ≤ r ∧ 1 ≤ j ∧ j ≤ c then
    M ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
  else false

/-- Equation (2): the two-dimensional XOR difference array
`D[i, j] = M[i, j] ⊕ M[i − 1, j] ⊕ M[i, j − 1] ⊕ M[i − 1, j − 1]` on `[r] × [c]` with the zero
padding. Index `(a, b) : Fin r × Fin c` is the paper's position `(a + 1, b + 1)`. -/
def xorDiff (M : Matrix (Fin r) (Fin c) Bool) : Matrix (Fin r) (Fin c) Bool :=
  fun a b =>
    xor (xor (padded M (a + 1) (b + 1)) (padded M a (b + 1)))
      (xor (padded M (a + 1) b) (padded M a b))

/-- The support `{(i, j) : A[i, j] = 1}` of a binary matrix, as a set of (0-based) cells. -/
def supp (A : Matrix (Fin r) (Fin c) Bool) : Finset (Fin r × Fin c) :=
  Finset.univ.filter (fun x => A x.1 x.2 = true)

/-- The 0/1 indicator matrix of a set of cells. -/
def indicator (P : Finset (Fin r × Fin c)) : Matrix (Fin r) (Fin c) Bool :=
  fun i j => decide ((i, j) ∈ P)

/-- Row-major order on cells: by row, then by column (lexicographic order on `(row, column)`). -/
def rowKey : Fin r × Fin c ≃ (Fin r ×ₗ Fin c) := toLex

/-- Column-major order on cells: by column, then by row (lexicographic order on
`(column, row)`). -/
def colKey : Fin r × Fin c ≃ (Fin c ×ₗ Fin r) := (Equiv.prodComm (Fin r) (Fin c)).trans toLex

/-- The cells of `P` as keys in row-major order. -/
def rowKeys (P : Finset (Fin r × Fin c)) : Finset (Fin r ×ₗ Fin c) :=
  P.map rowKey.toEmbedding

/-- The cells of `P` as keys in column-major order. -/
def colKeys (P : Finset (Fin r × Fin c)) : Finset (Fin c ×ₗ Fin r) :=
  P.map colKey.toEmbedding

/-- The bijection between the row-major and the column-major keys of the same cell. -/
def keySwap (P : Finset (Fin r × Fin c)) : rowKeys P ≃ colKeys P :=
  Equiv.subtypeEquiv (rowKey.symm.trans colKey) (by
    intro x
    simp [rowKeys, colKeys])

/-- §6.1, printed p. 21 (PDF p. 22): the rank permutation `σ_P ∈ S_m` (`m = |P|`). List `P` in
row-major order (row by row, left to right within a row) and in column-major order (column by
column, top to bottom within a column); `σ_P(a) = b` when the `a`-th point of the first list
is the `b`-th point of the second list. Positions are 0-based (`Fin m`). Points may share rows
and columns. -/
noncomputable def rankPerm (P : Finset (Fin r × Fin c)) : Equiv.Perm (Fin P.card) :=
  ((rowKeys P).orderIsoOfFin (by simp [rowKeys])).toEquiv.trans
    ((keySwap P).trans ((colKeys P).orderIsoOfFin (by simp [colKeys])).toEquiv.symm)

/-- `|P ∩ ([i] × [j])|` in the paper's 1-based coordinates (`[0] = ∅`). -/
def domCount (P : Finset (Fin r × Fin c)) (i j : ℕ) : ℕ :=
  (P.filter (fun x => (x.1 : ℕ) + 1 ≤ i ∧ (x.2 : ℕ) + 1 ≤ j)).card

/-- `|P ∩ ([i₁, i₂] × [j₁, j₂])|` in the paper's 1-based coordinates (inclusive intervals, empty
when `i₁ > i₂` or `j₁ > j₂`). -/
def rectCountP (P : Finset (Fin r × Fin c)) (i₁ i₂ j₁ j₂ : ℕ) : ℕ :=
  (P.filter (fun x => i₁ ≤ (x.1 : ℕ) + 1 ∧ (x.1 : ℕ) + 1 ≤ i₂ ∧
    j₁ ≤ (x.2 : ℕ) + 1 ∧ (x.2 : ℕ) + 1 ≤ j₂)).card

end Matrices

/-- Equation (13), §6.1, printed p. 21 (PDF p. 22): the board pattern `ρ_k ∈ S_{k²}`,
`ρ_k((p − 1)k + q) = (q − 1)k + p` for `p, q ∈ [k]`. With 0-based positions this is
`ρ_k(p k + q) = q k + p` for `p, q < k`. -/
def rho (k : ℕ) : Equiv.Perm (Fin (k * k)) :=
  finProdFinEquiv.symm.trans ((Equiv.prodComm (Fin k) (Fin k)).trans finProdFinEquiv)

/-! ## Constructor input layouts -/

/-- An explicit list of points (Lemma 6.2's "explicit P", Theorem 1.2's "supp(D) given
explicitly") in memory: memory words `2a` and `2a + 1` hold the (1-based) row and column of the
`a`-th listed point; all other words are zero. -/
def pointsMem (L : List (ℕ × ℕ)) (j : ℕ) : ℕ :=
  match L[j / 2]? with
  | none => 0
  | some x => if j % 2 = 0 then x.1 else x.2

/-- `L` lists the cells of `P` in 1-based coordinates, each exactly once, in arbitrary order. -/
def ListsCells {r c : ℕ} (P : Finset (Fin r × Fin c)) (L : List (ℕ × ℕ)) : Prop :=
  L.Nodup ∧ ∀ x : ℕ × ℕ, x ∈ L ↔ ∃ p ∈ P, x = ((p.1 : ℕ) + 1, (p.2 : ℕ) + 1)

/-- A list of rectangles `[a, b] × [p, q]` in memory: memory words `4u, 4u + 1, 4u + 2, 4u + 3`
hold `a, b, p, q` of the `u`-th rectangle; all other words are zero. -/
def rectsMem (L : List (ℕ × ℕ × ℕ × ℕ)) (j : ℕ) : ℕ :=
  match L[j / 4]? with
  | none => 0
  | some (a, b, p, q) =>
      if j % 4 = 0 then a else if j % 4 = 1 then b else if j % 4 = 2 then p else q

/-- The cell `(i, j)` (1-based) lies in the rectangle `[a, b] × [p, q]`. -/
def InRect (R : ℕ × ℕ × ℕ × ℕ) (i j : ℕ) : Prop :=
  R.1 ≤ i ∧ i ≤ R.2.1 ∧ R.2.2.1 ≤ j ∧ j ≤ R.2.2.2

/-- Theorem 1.2's rectangle input: `K` is a collection of rectangles `[a, b] × [p, q]` with
`1 ≤ a ≤ b ≤ r` and `1 ≤ p ≤ q ≤ c`, pairwise disjoint (any two list entries share no cell),
whose union is exactly the set of one-entries of `M`. -/
def ExactDisjointCover {r c : ℕ} (M : Matrix (Fin r) (Fin c) Bool)
    (K : List (ℕ × ℕ × ℕ × ℕ)) : Prop :=
  (∀ R ∈ K, 1 ≤ R.1 ∧ R.1 ≤ R.2.1 ∧ R.2.1 ≤ r ∧ 1 ≤ R.2.2.1 ∧ R.2.2.1 ≤ R.2.2.2 ∧
    R.2.2.2 ≤ c) ∧
  (∀ u v : Fin K.length, u ≠ v → ∀ i j : ℕ, ¬ (InRect K[u] i j ∧ InRect K[v] i j)) ∧
  ∀ (i : Fin r) (j : Fin c), M i j = true ↔ ∃ R ∈ K, InRect R ((i : ℕ) + 1) ((j : ℕ) + 1)

/-! ## Representations -/

/-- A packed bit buffer `bits` is an entry-access representation of `M` for the query program
`Q`: for every entry `(i, j) ∈ [r] × [c]`, the program run on memory `packBits w bits` with
registers `[r, c, |bits|, i, j]` halts within `T₀` steps with `r₀ = M[i, j]` (as `0/1`), and
within `T` steps when `n₀ ≤ r + c`. -/
def EntryRep {r c : ℕ} (w : ℕ) (Q : Program) (T T₀ n₀ : ℕ) (M : Matrix (Fin r) (Fin c) Bool)
    (bits : List Bool) : Prop :=
  ∀ (i : Fin r) (j : Fin c),
    RunsQuery w Q (packBits w bits) [r, c, bits.length, (i : ℕ) + 1, (j : ℕ) + 1]
      [if M i j then 1 else 0] T₀ ∧
    (n₀ ≤ r + c →
      RunsQuery w Q (packBits w bits) [r, c, bits.length, (i : ℕ) + 1, (j : ℕ) + 1]
        [if M i j then 1 else 0] T)

/-- A packed bit buffer `bits` is a counting representation of the cell set `P ⊆ [r] × [c]`
for the dominance program `domQ` and the rectangle program `rectQ`: for all cutoffs
`0 ≤ i ≤ r`, `0 ≤ j ≤ c`, `domQ` on registers `[r, c, |bits|, i, j]` returns
`|P ∩ ([i] × [j])|`, and for all `0 ≤ i₁, i₂ ≤ r`, `0 ≤ j₁, j₂ ≤ c`, `rectQ` on registers
`[r, c, |bits|, i₁, i₂, j₁, j₂]` returns `|P ∩ ([i₁, i₂] × [j₁, j₂])|`; each within `T₀` steps,
and within `T` steps when `n₀ ≤ r + c`. -/
def CountRep {r c : ℕ} (w : ℕ) (domQ rectQ : Program) (T T₀ n₀ : ℕ)
    (P : Finset (Fin r × Fin c)) (bits : List Bool) : Prop :=
  (∀ i j : ℕ, i ≤ r → j ≤ c →
    RunsQuery w domQ (packBits w bits) [r, c, bits.length, i, j] [domCount P i j] T₀ ∧
    (n₀ ≤ r + c →
      RunsQuery w domQ (packBits w bits) [r, c, bits.length, i, j] [domCount P i j] T)) ∧
  (∀ i₁ i₂ j₁ j₂ : ℕ, i₁ ≤ r → i₂ ≤ r → j₁ ≤ c → j₂ ≤ c →
    RunsQuery w rectQ (packBits w bits) [r, c, bits.length, i₁, i₂, j₁, j₂]
      [rectCountP P i₁ i₂ j₁ j₂] T₀ ∧
    (n₀ ≤ r + c →
      RunsQuery w rectQ (packBits w bits) [r, c, bits.length, i₁, i₂, j₁, j₂]
        [rectCountP P i₁ i₂ j₁ j₂] T))

end PatternRangeCounting1593.RangeCounting.Supplement


