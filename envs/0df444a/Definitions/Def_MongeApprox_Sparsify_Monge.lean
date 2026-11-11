-- Prove2me | Definitions.Def_MongeApprox_Sparsify_Monge
-- name    : MongeApprox_Sparsify_Monge
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:01:21.328512+00:00
-- url     : https://prove2.me/theorems/9129c8a9-6baf-4558-85b1-73c366b9d47e
-- title:
--   Monge matrices: density $M^\square$, core size $\delta$, total curvature $\kappa$, normalized and simple matrices, $(\alpha,K)$-approximation (§3 (3)–(4), Definition 7.1)
-- statement:
--   For a $p\times q$ matrix $M$ with finite real entries (rows and columns indexed from $0$, the row index growing downward), the **density matrix** is $M^\square_{ij}:=M_{i,j+1}+M_{i+1,j}-M_{ij}-M_{i+1,j+1}$ for $i\in[0..p-1)$, $j\in[0..q-1)$ (3). $M$ is **Monge** if $M^\square\ge 0$. The **core** is $\{(i,j,M^\square_{ij}) : M^\square_{ij}\ne 0\}$ and the **core size** $\delta(M)$ its cardinality; the **total curvature** is $\kappa(M):=\sum_{i=0}^{p-2}\sum_{j=0}^{q-2}M^\square_{ij}$ (4). $M$ is **normalized** if every entry is $0$ or at least $1$, **integer-valued** if every entry is an integer, and **simple** if it is Monge and its bottom row (row $p-1$) and leftmost column (column $0$) are zero. For $K\in[0,+\infty]$ and $\alpha\ge1$, $\widehat M$ **$(\alpha,K)$-approximates** $M$ (Definition 7.1) if $M_{ij}\le\widehat M_{ij}$ for every entry and $\widehat M_{ij}\le\alpha M_{ij}$ whenever $M_{ij}\le K$.
--
--   **Formalization Note.** Matrices are `Matrix (Fin p) (Fin q) ℝ`. `density M i j` is a function of two naturals equal to $M^\square_{ij}$ inside $[0..p-1)\times[0..q-1)$ and $0$ elsewhere; `densityZ M` is the same on $\mathbb Z^2$ (zero at negative positions). `coreSet M` is the finset of positions with nonzero density and `coreSize M` its cardinality (the core of triples has the same cardinality). `IsNormalized` (every entry $=0$ or $\ge1$) implies nonnegativity; `IsNonneg` is stated separately. The threshold $K$ has type `ℝ≥0∞` (exactly $[0,+\infty]$); `LeThreshold x K` is $x\le K$ (true when $K=+\infty$) and `minThreshold K x` is $\min\{K,x\}$. `Approximates α K M M̂` does not bundle nonnegativity of the two matrices (the paper defines the relation for nonnegative matrices; every statement using it assumes $M\ge0$ and proves $\widehat M\ge M$).
-- source:
--   Gorbachev 2026, Edit Distance Approximation: Subquadratic Factor Three and Monge Approximation Schemes (PDF sha256 b7eeb435…), §3 Matrix Tools, (3), (4), printed pp. 14–15 (PDF 16–17); Definition 7.1, printed p. 34 (PDF 36); simple matrices, proof sketch of Theorem 7.3, printed p. 35 (PDF 37)

import Mathlib

/-!
# Monge matrices, density, core, total curvature, simple matrices, (α, K)-approximation

Gorbachev, *Edit Distance Approximation: Subquadratic Factor Three and Monge Approximation Schemes*
(2026, PDF sha256 b7eeb435…), §3 "Matrix Tools", printed pp. 14–15 (PDF 16–17), (3)–(5);
§7, Definition 7.1, printed p. 34 (PDF 36); "simple" from the proof sketch of Theorem 7.3,
printed p. 35 (PDF 37).

Conventions.
* A `p × q` matrix with finite real entries is `Matrix (Fin p) (Fin q) ℝ`; rows and columns are
  indexed from `0`, and the row index grows downward (row `p − 1` is the bottom row, column `0`
  the leftmost column).
* `density M i j` is `M□_ij := M_{i,j+1} + M_{i+1,j} − M_ij − M_{i+1,j+1}` for
  `i ∈ [0..p−1)`, `j ∈ [0..q−1)` (3), and `0` at every other pair of naturals (positions outside
  the density matrix have no mass). `densityZ M` is the same function on positions `(a, b) ∈ ℤ²`.
* `IsMonge M`: every entry of `M□` is nonnegative. A matrix with one row or one column has an
  empty density matrix and is Monge.
* `coreSet M` is the set of positions `(i, j)` of nonzero density entries; `coreSize M = δ(M)` is
  its cardinality (the core itself is the set of triples `(i, j, M□_ij)`, which has the same
  cardinality). `totalCurvature M = κ(M)` is the sum of all density entries (4).
* `IsNormalized M`: every entry is `0` or at least `1` (the paper defines normalized for
  nonnegative matrices; this predicate implies nonnegativity).
* `IsSimple M`: `M` is Monge and its bottom row and leftmost column are zero.
* `K ∈ [0, +∞]` is `K : ℝ≥0∞`. `LeThreshold x K` is `x ≤ K` for a real `x` (true when `K = ⊤`);
  `minThreshold K x` is `min{K, x}` as a real for a finite `x` (`= x` when `K = ⊤`).
* `Approximates α K M M̂` is Definition 7.1: `M_ij ≤ M̂_ij` for every entry and
  `M̂_ij ≤ α M_ij` whenever `M_ij ≤ K`. The definition applies to nonnegative matrices; every
  statement that uses it assumes nonnegativity of `M` itself.
-/

namespace MongeApprox.Sparsify

open scoped ENNReal

variable {p q : ℕ}

/-- The density matrix `M□` of (3), as a function of two naturals: `M□_ij` when `i + 1 < p` and
`j + 1 < q`, and `0` elsewhere. -/
def density (M : Matrix (Fin p) (Fin q) ℝ) (i j : ℕ) : ℝ :=
  if h : i + 1 < p ∧ j + 1 < q then
    M ⟨i, by omega⟩ ⟨j + 1, h.2⟩ + M ⟨i + 1, h.1⟩ ⟨j, by omega⟩
      - M ⟨i, by omega⟩ ⟨j, by omega⟩ - M ⟨i + 1, h.1⟩ ⟨j + 1, h.2⟩
  else 0

/-- The density matrix on positions of `ℤ²`: `M□_ab` for `(a, b) ∈ [0..p−1) × [0..q−1)`, and `0`
at every other position. -/
def densityZ (M : Matrix (Fin p) (Fin q) ℝ) (z : ℤ × ℤ) : ℝ :=
  if 0 ≤ z.1 ∧ 0 ≤ z.2 then density M z.1.toNat z.2.toNat else 0

/-- `M` is Monge: every entry of its density matrix is nonnegative. -/
def IsMonge (M : Matrix (Fin p) (Fin q) ℝ) : Prop :=
  ∀ i j : ℕ, i + 1 < p → j + 1 < q → 0 ≤ density M i j

/-- The positions of the core: `(i, j) ∈ [0..p−1) × [0..q−1)` with `M□_ij ≠ 0`. -/
noncomputable def coreSet (M : Matrix (Fin p) (Fin q) ℝ) : Finset (ℕ × ℕ) :=
  open Classical in
  (Finset.range (p - 1) ×ˢ Finset.range (q - 1)).filter fun ij => density M ij.1 ij.2 ≠ 0

/-- The core size `δ(M) := |core(M)|`, the number of nonzero density entries. -/
noncomputable def coreSize (M : Matrix (Fin p) (Fin q) ℝ) : ℕ :=
  (coreSet M).card

/-- The total curvature `κ(M) := Σ_{i=0}^{p−2} Σ_{j=0}^{q−2} M□_ij` (left-hand side of (4)). -/
def totalCurvature (M : Matrix (Fin p) (Fin q) ℝ) : ℝ :=
  ∑ i ∈ Finset.range (p - 1), ∑ j ∈ Finset.range (q - 1), density M i j

/-- Every entry is nonnegative. -/
def IsNonneg (M : Matrix (Fin p) (Fin q) ℝ) : Prop :=
  ∀ i j, 0 ≤ M i j

/-- Normalized: every entry is either zero or at least one. -/
def IsNormalized (M : Matrix (Fin p) (Fin q) ℝ) : Prop :=
  ∀ i j, M i j = 0 ∨ 1 ≤ M i j

/-- Integer-valued: every entry is an integer. -/
def IsIntegerValued (M : Matrix (Fin p) (Fin q) ℝ) : Prop :=
  ∀ i j, ∃ z : ℤ, M i j = z

/-- A simple Monge matrix: Monge, with all entries of the bottom row (row `p − 1`) and of the
leftmost column (column `0`) equal to zero. -/
def IsSimple (M : Matrix (Fin p) (Fin q) ℝ) : Prop :=
  IsMonge M ∧ (∀ (i : Fin p) (j : Fin q), (i : ℕ) + 1 = p → M i j = 0) ∧
    (∀ (i : Fin p) (j : Fin q), (j : ℕ) = 0 → M i j = 0)

/-- `x ≤ K` for a real `x` and a threshold `K ∈ [0, +∞]`; always true when `K = +∞`. -/
def LeThreshold (x : ℝ) (K : ℝ≥0∞) : Prop :=
  K = ⊤ ∨ x ≤ K.toReal

/-- `min{K, x}` for a threshold `K ∈ [0, +∞]` and a real `x`: `x` when `K = +∞`. -/
noncomputable def minThreshold (K : ℝ≥0∞) (x : ℝ) : ℝ :=
  if K = ⊤ then x else min K.toReal x

/-- Definition 7.1: `M̂` `(α, K)`-approximates `M` (`M ⪯^α_K M̂`): `M_ij ≤ M̂_ij` for every entry,
and `M̂_ij ≤ α M_ij` whenever `M_ij ≤ K`. With `K = ⊤` this is `M ≤ M̂ ≤ αM` entrywise. -/
def Approximates (α : ℝ) (K : ℝ≥0∞) (M Mhat : Matrix (Fin p) (Fin q) ℝ) : Prop :=
  ∀ i j, M i j ≤ Mhat i j ∧ (LeThreshold (M i j) K → Mhat i j ≤ α * M i j)

end MongeApprox.Sparsify


