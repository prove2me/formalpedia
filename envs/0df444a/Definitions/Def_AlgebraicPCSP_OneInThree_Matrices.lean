-- Prove2me | Definitions.Def_AlgebraicPCSP_OneInThree_Matrices
-- name    : AlgebraicPCSP_OneInThree_Matrices
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:27.559856+00:00
-- url     : https://prove2.me/theorems/1b4eeced-e989-4dec-8f41-b2820fcc4bea
-- title:
--   The operation t, area, g-equivalence, tameness, covers, ⟨i⟩ and almost rectangles (§8.1–8.3)
-- statement:
--   Fix a set $D$, a prime-arity operation $s:D^p\to D$, a map $f:\{0,1\}\to D$ and a map $g:D\to\{0,1\}$. All matrices below are $p\times p$ with rows and columns indexed by $1,\dots,p$; $x_{ij}$ is the entry in row $i$, column $j$.
--
--   1. **The operation $t$** (p. 53) of arity $p^2$ is
--   $$t(x_{11},x_{12},\dots,x_{1p},x_{21},\dots,x_{pp})=s\big(s(x_{11},\dots,x_{p1}),\,s(x_{12},\dots,x_{p2}),\,\dots,\,s(x_{1p},\dots,x_{pp})\big):$$
--   on the matrix $X=(x_{ij})$, apply $s$ to each column and then $s$ to the row of results. Its $p^2$ arguments are listed in row-major order.
--   2. **Area** (Definition 8.5). For a zero-one matrix $X$, $\lambda(X)=\big(\sum_{i,j}x_{ij}\big)/p^2$, a rational number.
--   3. **$g$-equivalence** (Definition 8.5). Zero-one matrices $X,Y$ are $g$-equivalent, $X\sim Y$, if $g(t(X))=g(t(Y))$, where a zero-one matrix is evaluated in $D$ entrywise through $f$.
--   4. **Tame** (Definition 8.5). $X$ is tame if either $X\sim 0_{p\times p}$ and $\lambda(X)<1/3$, or $X\sim 1_{p\times p}$ and $\lambda(X)>1/3$; here $0_{p\times p}$ and $1_{p\times p}$ are the all-zero and all-one matrices.
--   5. **Cover** (Definition 8.6). Zero-one matrices $X,Y,Z$ form a cover if for every $i,j$ exactly one of $x_{ij},y_{ij},z_{ij}$ equals $1$.
--   6. **$\langle k\rangle$** (§8.2). The $p^2$-tuple $\langle k\rangle=(1,\dots,1,0,\dots,0)$ with ones exactly in its first $k$ positions, read as a matrix in row-major order (for $k\ge p^2$ it is all ones).
--   7. **$[k_1,\dots,k_p]$** (Definition 8.11). The zero-one matrix whose $j$-th column begins with $k_j$ ones followed by $p-k_j$ zeros, $0\le k_j\le p$.
--   8. **Almost rectangle** (Definition 8.11). A matrix $[k,\dots,k,l,\dots,l]$ with $m$ columns of height $k$ followed by $p-m$ columns of height $l$, where $0\le m\le p$, $0\le l\le k\le p$, and the *size of the step* $k-l$ is at most a bound $b$; the paper takes $b=5|D|$.
--   9. The $p$-tuple with ones in its first $l$ positions and zeros after (§8.4).
--
--   These are the combinatorial objects of the proof of Theorem 8.1: every lemma of §8.2–8.4 is a statement about $g$-equivalence and tameness of such matrices.
--
--   **Formalization Note** Matrices are functions `Fin p → Fin p → Fin 2` (row index first, from $0$). The row-major reading of a $p^2$-tuple uses `finProdFinEquiv`, which sends $(i,j)$ to the index $p\,i+j$. $g$-equivalence evaluates `t` on `fun i j => f (X i j)`: the paper instead renames $D$ so that $f(0)=0$, $f(1)=1$, which is the same thing. Definition 8.11 in the paper says $1\le k_i\le p$, but its own proofs use columns of height $0$ (Lemma 8.14's $Y_i$, by (8.1)); the definition here allows $0\le k_i\le p$.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 53 (operation t, Definition 8.5); p. 54 (Definition 8.6, tuples ⟨i⟩); p. 55 (Definition 8.11); pp. 57–58 (§8.4)

import Mathlib

namespace AlgebraicPCSP.OneInThree

/-- The operation `t` of arity `p²` built from `s : Dᵖ → D` (§8.1, p. 53), read on a
`p × p` matrix `X` (entry `X i j` in row `i`, column `j`): apply `s` to every column vector
and then `s` to the resulting row vector,
`t(X) = s(s(x₁₁, …, x_p₁), s(x₁₂, …, x_p₂), …, s(x₁ₚ, …, x_pp))`. -/
def tOp {D : Type} {p : ℕ} (s : (Fin p → D) → D) (X : Fin p → Fin p → D) : D :=
  s (fun j => s (fun i => X i j))

/-- The `p × p` matrix whose rows are read off a `p²`-tuple in row-major order: entry
`(i, j)` is the coordinate with index `p·i + j` (`finProdFinEquiv (i, j) = j + p * i`), so
the tuple is `(x₁₁, x₁₂, …, x₁ₚ, x₂₁, …, x_pp)` (p. 53). -/
def toMatrix {α : Type} {p : ℕ} (x : Fin (p * p) → α) : Fin p → Fin p → α :=
  fun i j => x (finProdFinEquiv (i, j))

/-- `t` as a `p²`-ary operation on its argument tuple
`(x₁₁, x₁₂, …, x₁ₚ, x₂₁, x₂₂, …, x₂ₚ, x₃₁, …, x_pp)` (p. 53). -/
def tFlat {D : Type} {p : ℕ} (s : (Fin p → D) → D) : (Fin (p * p) → D) → D :=
  fun x => tOp s (toMatrix x)

/-- The area of a zero-one `p × p` matrix (Definition 8.5, p. 53): the fraction of ones,
`λ(X) = (∑_{i,j} x_ij) / p²`, a rational number. -/
def area {p : ℕ} (X : Fin p → Fin p → Fin 2) : ℚ :=
  (∑ i, ∑ j, ((X i j).val : ℚ)) / (p : ℚ) ^ 2

/-- `g`-equivalence of zero-one matrices (Definition 8.5, p. 53), `X ∼ Y` iff
`g(t(X)) = g(t(Y))`. A zero-one matrix is evaluated in `D` through `f : {0, 1} → D`, i.e.
`t` is applied to the matrix `f ∘ X` (the paper identifies `0, 1` with `f(0), f(1) ∈ D`). -/
def GEquiv {D : Type} {p : ℕ} (f : Fin 2 → D) (g : D → Fin 2) (s : (Fin p → D) → D)
    (X Y : Fin p → Fin p → Fin 2) : Prop :=
  g (tOp s (fun i j => f (X i j))) = g (tOp s (fun i j => f (Y i j)))

/-- The zero matrix `0_{p×p}`. -/
def zeroMat (p : ℕ) : Fin p → Fin p → Fin 2 := fun _ _ => 0

/-- The all-ones matrix `1_{p×p}`. -/
def oneMat (p : ℕ) : Fin p → Fin p → Fin 2 := fun _ _ => 1

/-- A zero-one matrix `X` is tame (Definition 8.5, p. 53) if either `X ∼ 0_{p×p}` and
`λ(X) < 1/3`, or `X ∼ 1_{p×p}` and `λ(X) > 1/3`. -/
def IsTame {D : Type} {p : ℕ} (f : Fin 2 → D) (g : D → Fin 2) (s : (Fin p → D) → D)
    (X : Fin p → Fin p → Fin 2) : Prop :=
  (GEquiv f g s X (zeroMat p) ∧ area X < 1 / 3) ∨
    (GEquiv f g s X (oneMat p) ∧ 1 / 3 < area X)

/-- A triple `X, Y, Z` of `p × p` zero-one matrices is a cover (Definition 8.6, p. 54) if for
every `i, j` exactly one of `x_ij, y_ij, z_ij` equals one (equivalently, their sum is `1`). -/
def IsCover {p : ℕ} (X Y Z : Fin p → Fin p → Fin 2) : Prop :=
  ∀ i j, (X i j).val + (Y i j).val + (Z i j).val = 1

/-- The `p²`-tuple `⟨k⟩ = (1, …, 1, 0, …, 0)` with ones in its first `k` positions (§8.2,
p. 54); for `k ≥ p²` it is the all-ones tuple. -/
def segTuple (p k : ℕ) : Fin (p * p) → Fin 2 := fun x => if x.val < k then 1 else 0

/-- The tuple `⟨k⟩` as a `p × p` matrix in row-major order: the first `⌊k/p⌋` rows are ones,
the next row starts with `k mod p` ones, and all other entries are zero. -/
def seg (p k : ℕ) : Fin p → Fin p → Fin 2 := toMatrix (segTuple p k)

/-- The matrix `[k₁, …, kₚ]` (Definition 8.11, p. 55): its `j`-th column begins with `k_j`
ones followed by `p − k_j` zeros, i.e. entry `(i, j)` is `1` iff `i < k_j` (rows indexed
from `0`). -/
def colMatrix (p : ℕ) (k : Fin p → ℕ) : Fin p → Fin p → Fin 2 :=
  fun i j => if i.val < k j then 1 else 0

/-- An almost rectangle with step bound `b` (Definition 8.11, p. 55; the paper takes
`b = 5|D|`): a matrix `[k, …, k, l, …, l]` with `m` columns of height `k` followed by `p − m`
columns of height `l`, where `0 ≤ m ≤ p`, `0 ≤ l ≤ k ≤ p` and the size of the step `k − l` is
at most `b`. -/
def IsAlmostRectangle (b : ℕ) {p : ℕ} (X : Fin p → Fin p → Fin 2) : Prop :=
  ∃ k l m : ℕ, l ≤ k ∧ k ≤ p ∧ m ≤ p ∧ k - l ≤ b ∧
    X = colMatrix p (fun j => if j.val < m then k else l)

/-- The `p`-tuple `(1, …, 1, 0, …, 0)` with ones in its first `l` positions (§8.4, p. 58). -/
def prefixOnes (p l : ℕ) : Fin p → Fin 2 := fun j => if j.val < l then 1 else 0

end AlgebraicPCSP.OneInThree


