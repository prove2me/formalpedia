-- Prove2me | Definitions.Def_ErrAmpOV_Supplement_SORT
-- name    : ErrAmpOV_Supplement_SORT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:15:44.929439+00:00
-- url     : https://prove2.me/theorems/52567cde-3914-486e-b11b-54eeb2b68bd4
-- title:
--   The sorting search problem $\mathrm{SORT}_{n,m}$ and its bit encoding
-- statement:
--   Fix $n,m\in\mathbb N$ and a bit width $w$ (the supplement always takes $w=\lceil\log_2 m\rceil$). An input $x\in[m]^n$, where $[m]=\{0,1,\dots,m-1\}$, is written as $n$ blocks of $w$ bits: bit $j$ of block $i$ is $x(i,j)$, and block $i$ has value
--   $$\mathrm{val}_i(x)=\sum_{j<w}2^j\,[x(i,j)=1]$$
--   (little-endian). The input is **valid** when every block has value less than $m$, i.e. it encodes a point of $[m]^n$.
--
--   A list $y$ of $n$ blocks is the **sorted version** of $x$, written $(x,y)\in\mathrm{SORT}_{n,m}$, when $y$ is obtained from $x$ by permuting its blocks and the values $\mathrm{val}_0(y)\le\mathrm{val}_1(y)\le\dots\le\mathrm{val}_{n-1}(y)$ are non-decreasing. Because the encoding of a value is unique, $y$ is unique; it is $\mathrm{SORT}_{n,m}(x)$. Its output string is the $n\cdot w$ bits of $y$, block by block and bit by bit.
--
--   This is the search problem of Theorems 4.1 and 5.1.
--
--   **Formalization Note** The paper's "log(m) bits" (footnote 2) is $\lceil\log_2 m\rceil$ bits when $m$ is not a power of two. Circuits for SORT are only required to be correct on valid inputs, since the paper's domain is $[m]^n$.
-- source:
--   Koucký, Mertz, Rajgopal, Efficient Error Amplification for Sorting and Orthogonal Vectors, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3), §2.2, p.6 (unnumbered definition of SORT_{n,m}, footnote 2)

import Mathlib

set_option autoImplicit false

namespace ErrAmpOV.Supplement

/-!
# The sorting search problem `SORT_{n,m}` and its bit encoding

Source: Koucký, Mertz, Rajgopal, *Efficient Error Amplification for Sorting and Orthogonal
Vectors*, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3),
§2.2, p.6 (unnumbered: "sorting a set of `n` integers over `[m] := {0, 1, …, m − 1}` …
`(x, y) ∈ SORT_{n,m}` iff `y` has the elements of `x` in non-decreasing order"; footnote 2:
"representing any element in `[m]` with `log(m)` bits").

**Formalization Note.**
* An input `x ∈ [m]^n` is written in `n·w` bits, `x (i, j)` being bit `j` of element `i`,
  little-endian: element `i` has value `elemVal (fun j => x (i, j)) = Σ_j 2^j·[x (i, j)]`.
  The width `w` is `Nat.clog 2 m` (the paper's "`log(m)` bits", rounded up when `m` is not
  a power of two); the statements of the supplement fix `w := Nat.clog 2 m`.
* `SortValid n m w x`: every element of `x` is `< m`, i.e. `x` encodes a point of `[m]^n`.
  The paper's domain is `[m]^n`, so circuits are only required to be correct on valid inputs.
* `IsSortOf n w x y`: `y` lists the elements of `x` (as bit blocks) in non-decreasing order of
  value, i.e. `y` is `x` with its `n` blocks permuted and the values are monotone. Since the
  encoding of a value is unique, `y` is unique: this is `y = SORT_{n,m}(x)`.
* `sortEncode n w y` is the output string: blocks `0, …, n−1` in order, each block's bits
  `0, …, w−1` in order (`n·w` bits).
-/

/-- The value of a `w`-bit block, little-endian: `Σ_{j<w} 2^j·[b j]`. -/
def elemVal {w : ℕ} (b : Fin w → Bool) : ℕ :=
  ∑ j : Fin w, if b j then 2 ^ (j : ℕ) else 0

/-- `x` encodes an element of `[m]^n`: each of its `n` blocks has value `< m`. -/
def SortValid (n m w : ℕ) (x : Fin n × Fin w → Bool) : Prop :=
  ∀ i : Fin n, elemVal (fun j => x (i, j)) < m

/-- `(x, y) ∈ SORT`: `y` is the list of blocks of `x` rearranged in non-decreasing order of
value. -/
def IsSortOf (n w : ℕ) (x y : Fin n × Fin w → Bool) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), (∀ i j, y (i, j) = x (σ i, j)) ∧
    Monotone (fun i : Fin n => elemVal (fun j => y (i, j)))

/-- The `n·w`-bit output string of a list of `n` blocks: block by block, bit by bit. -/
def sortEncode (n w : ℕ) (y : Fin n × Fin w → Bool) : List Bool :=
  (List.ofFn fun i : Fin n => List.ofFn fun j : Fin w => y (i, j)).flatten

end ErrAmpOV.Supplement


