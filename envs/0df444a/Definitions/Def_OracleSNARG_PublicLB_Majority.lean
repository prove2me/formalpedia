-- Prove2me | Definitions.Def_OracleSNARG_PublicLB_Majority
-- name    : OracleSNARG_PublicLB_Majority
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:45:11.176688+00:00
-- url     : https://prove2.me/theorems/47c2001a-8062-463e-8de1-6518265224dc
-- title:
--   Boolean oracles, the majority computation $C^O(x)=\mathrm{Maj}(O(x,1),\dots,O(x,N))$, purported executions, $\mathrm{err}_O$ and $\varepsilon$-robustness (Definitions 15-16, §6)
-- statement:
--   An **oracle** is a function $O:\{0,1\}^*\to\{0,1\}$. A query $(x,i)$, with $x$ a bit string and $i$ a row position, is sent to the oracle as the bit string $\mathrm{enc}(x,i)=1^i\,0\,x$; this encoding is injective and efficiently decodable (`pairDec` inverts it).
--
--   For $N\ge 0$ the **row indexed by $x$** is the vector $(O(x,0),\dots,O(x,N-1))\in\{0,1\}^N$. For a vector $a\in\{0,1\}^N$, $\mathrm{Maj}(a)=1$ iff strictly more than $N/2$ of its entries are $1$, that is iff $N<2\cdot|\{i:a_i=1\}|$. The **majority computation** of §6 is
--   $$C^O(x)=\mathrm{Maj}\big(O(x,0),\dots,O(x,N-1)\big),$$
--   a deterministic computation with $q=N$ non-adaptive oracle calls; its language is $L^O=\{x: C^O(x)=1\}$.
--
--   **Purported executions and errors (Definition 15).** A purported execution of $C^O$ on $x$ makes the fixed queries $(x,0),\dots,(x,N-1)$ but may use any answers, so it is an answer vector $a\in\{0,1\}^N$; it is accepting iff $\mathrm{Maj}(a)=1$, it has $q(\tau)=N$ oracle calls, and
--   $$\mathrm{err}_O(a)=\big|\{i<N: a_i\ne O(x,i)\}\big|.$$
--
--   **Robustness (Definition 16).** For a real $\varepsilon$, $C^O$ is **$\varepsilon$-robust on $x$** if $C^O(x)=1$, or every accepting $a$ satisfies $\mathrm{err}_O(a)\ge \varepsilon N$. The paper takes $\varepsilon\in(0,1]$; the range is imposed by the statements that use the notion.
--
--   **Formalization Note.** The oracle is `List Bool → Bool`; rows are `Fin N → Bool`, so the paper's positions $1,\dots,N$ are $0,\dots,N-1$. The answer-vector view of a purported execution is exact for this computation: its control flow does not depend on the answers.
-- source:
--   Goldwasser, Kalai, Incrementally Verifiable Oracle Aided Computation, STOC 2027 submission (manuscript sha256 cc66f0af…), p. 16, Definitions 15-16; p. 25, §6 (the computation C^O)

import Mathlib

set_option autoImplicit false

namespace OracleSNARG.PublicLB

/-- **Boolean oracle.** Goldwasser, Kalai, *Incrementally Verifiable Oracle Aided Computation*,
STOC 2027 submission (manuscript sha256 cc66f0af…), §6, p. 25: "Consider a Boolean oracle whose
queries are pairs (x, i)". An oracle answers every bit string `u ∈ {0,1}*` with one bit `O(u)`. -/
abbrev Oracle : Type := List Bool → Bool

/-- **The query `(x, i)` as a bit string.** One fixed injective, efficiently computable and
efficiently decodable encoding of pairs: `enc(x, i) = 1^i ∥ 0 ∥ x`. Row positions are
`i = 0, …, N − 1` (the paper's `i ∈ [N] = {1, …, N}`, shifted by one). -/
def pairEnc (x : List Bool) (i : ℕ) : List Bool :=
  List.replicate i true ++ false :: x

/-- Decoding of `pairEnc`: `pairDec q = some (x, i)` exactly when `q = pairEnc x i`. -/
def pairDec : List Bool → Option (List Bool × ℕ)
  | [] => none
  | false :: x => some (x, 0)
  | true :: q => (pairDec q).map fun p => (p.1, p.2 + 1)

/-- **The row indexed by `x`** (§6, p. 25): `(O(x,1), …, O(x,N))`, as a vector indexed by
`Fin N`. -/
def row (O : Oracle) (N : ℕ) (x : List Bool) : Fin N → Bool :=
  fun i => O (pairEnc x i.val)

/-- Number of ones of a bit vector of length `N`. -/
def ones {N : ℕ} (a : Fin N → Bool) : ℕ :=
  (Finset.univ.filter fun i => a i = true).card

/-- **Majority** `Maj(a₁, …, a_N)`: `1` iff strictly more than `N/2` of the entries are `1`. -/
def maj {N : ℕ} (a : Fin N → Bool) : Bool :=
  decide (N < 2 * ones a)

/-- **The majority computation** (§6, p. 25): `C^O(x) = Maj(O(x,1), …, O(x,N))`. It makes the
`q = N` non-adaptive oracle calls `(x,1), …, (x,N)` and outputs their majority. Its language is
`L^O = {x : C^O(x) = 1}`; the paper applies it to `x ∈ {0,1}^n`. -/
def C (O : Oracle) (N : ℕ) (x : List Bool) : Bool :=
  maj (row O N x)

/-- **`err_O` of a purported execution** (Definition 15, p. 16) for the majority computation. A
purported execution of `C^O` on `x` follows the fixed query sequence `(x,1), …, (x,N)` and may use
any answer at each oracle step, so it is exactly an answer vector `a ∈ {0,1}^N`; it is accepting iff
`Maj(a) = 1`, it makes `q(τ) = N` oracle calls, and
`err_O(a) = |{i ∈ [N] : a_i ≠ O(x,i)}|`. -/
def err (O : Oracle) (N : ℕ) (x : List Bool) (a : Fin N → Bool) : ℕ :=
  (Finset.univ.filter fun i => a i ≠ row O N x i).card

/-- **`ε`-robustness** (Definition 16, p. 16) of the majority computation on input `x`: either
`x ∈ L^O` (`C^O(x) = 1`), or every accepting purported execution `a` (`Maj(a) = 1`) satisfies
`err_O(a) ≥ ε q(τ) = ε N`. The paper takes `ε ∈ (0, 1]`; the range is imposed where the notion is
used. -/
def Robust (ε : ℝ) (O : Oracle) (N : ℕ) (x : List Bool) : Prop :=
  C O N x = true ∨ ∀ a : Fin N → Bool, maj a = true → ε * (N : ℝ) ≤ (err O N x a : ℝ)

end OracleSNARG.PublicLB


