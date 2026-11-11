-- Prove2me | Definitions.Def_FTConnOracle_Main_Codes
-- name    : FTConnOracle_Main_Codes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:26:37.397213+00:00
-- url     : https://prove2.me/theorems/29986a7c-bb6a-440e-b4a7-9646c9e5fdc4
-- title:
--   Bit-string codes of numbers, graphs, bipartite graphs and mask identifiers for the polynomial-time clauses
-- statement:
--   The paper's polynomial-time claims (Theorem 1.1, last sentence; Lemma 4.1, last sentence; Lemma 4.6, items 1 and 3) name no machine model. The machine is the published `LowErrExt.IsPolyTime`: one Turing machine computing a function from tuples of bit strings to bit strings in time polynomial in the input length. This module fixes how the paper's objects are written for it:
--
--   1. a number $k$ is written in unary, $1^k$;
--   2. a graph $G$ on $[n]$ is written as its $\binom n2$ adjacency bits $[\{i,j\}\in E(G)]$ for the pairs $i<j$ in lexicographic order;
--   3. the input of $(n,f,G)$ (Theorem 1.1) is the tuple $(1^n,1^f,\text{adjacency bits of }G)$, of length $\Theta(n^2)$ since $f\le\binom n2$; the input of $(n,G)$ (Lemma 4.6, item 3) is $(1^n,\text{adjacency bits of }G)$; the input of $(n,t)$ (Lemma 4.1) is $(1^n,1^t)$;
--   4. a bipartite graph $B$ with left side $[n]$ and right side $[r]$ is written as $1^r0$ followed by its $r\times n$ incidence matrix row by row;
--   5. an $m$-bit identifier is the list of its $m$ bits, and the input of $(n,x)$ for an $(n-1)$-bit identifier $x$ (Lemma 4.6, item 1) is $(1^n,x)$.
--
--   **Formalization Note.** `unary`, `adjBits`, `oracleInput f G`, `graphInput G`, `expanderInput n t`, `incidenceCode B`, `idBits x`, `maskInput n x`. Every code is injective for fixed $n$.
-- source:
--   Parter, Tzalik, Deterministic Fault-Tolerant Connectivity Oracles with Subqadratic Space, STOC 2027 submission (manuscript sha256 168306b7…), p. 3 (PDF 5) Theorem 1.1 last sentence; p. 16 (PDF 18) Lemma 4.1 last sentence; p. 23 (PDF 25) Lemma 4.6 items 1 and 3

import Mathlib

namespace FTConnOracle.Main

/-!
# Input and output codes for the polynomial-time clauses

Parter, Tzalik, *Deterministic Fault-Tolerant Connectivity Oracles with Subqadratic Space*,
STOC 2027 submission (manuscript sha256 168306b7…): Theorem 1.1 last sentence (p. 3, PDF 5),
Lemma 4.1 last sentence (p. 16, PDF 18), Lemma 4.6 items 1 and 3 (p. 23, PDF 25).

The paper names no machine model. The machine is the published `LowErrExt.IsPolyTime`
(one Turing machine, Mathlib's `Turing.TM2ComputableInPolyTime`, on tuples of bit strings), and
this module fixes how the paper's objects are written as such tuples:

* a number `k` in unary, `1^k`;
* a graph `G` on `[n]` as its adjacency bits of the pairs `i < j` in lexicographic order
  (`n(n−1)/2` bits);
* a bipartite graph `B` with left side `[n]` and right side `[r]` as `1^r 0` followed by its
  `r × n` incidence matrix row by row;
* an `m`-bit identifier as the list of its `m` bits.
-/

/-- A number `k` written in unary, `1^k`. -/
def unary (k : ℕ) : List Bool :=
  List.replicate k true

open Classical in
/-- The adjacency bits of `G`: for the pairs `i < j` of `[n]` in lexicographic order, the bit
`[{i, j} ∈ E(G)]`. -/
noncomputable def adjBits {n : ℕ} (G : SimpleGraph (Fin n)) : List Bool :=
  (List.finRange n).flatMap fun i =>
    ((List.finRange n).filter fun j => decide (i < j)).map fun j => decide (G.Adj i j)

/-- The input code of `(n, f, G)` (Theorem 1.1): `n` in unary, `f` in unary, the adjacency bits
of `G`. -/
noncomputable def oracleInput {n : ℕ} (f : ℕ) (G : SimpleGraph (Fin n)) : List (List Bool) :=
  [unary n, unary f, adjBits G]

/-- The input code of `(n, G)` (Lemma 4.6, item 3): `n` in unary, the adjacency bits of `G`. -/
noncomputable def graphInput {n : ℕ} (G : SimpleGraph (Fin n)) : List (List Bool) :=
  [unary n, adjBits G]

/-- The input code of `(n, t)` (Lemma 4.1): `n` and `t` in unary. -/
def expanderInput (n t : ℕ) : List (List Bool) :=
  [unary n, unary t]

/-- The code of a bipartite graph `B` with left side `[n]` and right side `[r]` (right
neighbourhoods `B v`): `1^r 0`, then the bits `[j ∈ B v]` for `j ∈ [r]` (rows) and `v ∈ [n]`
(columns), row by row. -/
def incidenceCode {n r : ℕ} (B : Fin n → Finset (Fin r)) : List Bool :=
  unary r ++ [false] ++
    (List.finRange r).flatMap fun j => (List.finRange n).map fun v => decide (j ∈ B v)

/-- An `m`-bit identifier as the list of its bits. -/
def idBits {m : ℕ} (x : Fin m → Bool) : List Bool :=
  List.ofFn x

/-- The input code of `(n, x)` for an `(n − 1)`-bit identifier `x` (Lemma 4.6, item 1). -/
def maskInput (n : ℕ) (x : Fin (n - 1) → Bool) : List (List Bool) :=
  [unary n, idBits x]

end FTConnOracle.Main


