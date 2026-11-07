-- Prove2me | Definitions.Def_RelQueryPTime_Encoding
-- name    : RelQueryPTime_Encoding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:40:15.133968+00:00
-- url     : https://prove2.me/theorems/f2dbb807-ff3b-44d3-8da1-a0ac49ea90a4
-- title:
--   Encoding $\langle B, c\rangle$ of an ordered database with constants, and $\mathrm{Graph}(Q)$
-- statement:
--   For an ordered database $B$ of scheme $\sigma$ with $n$ elements and an $r$-tuple $\bar c = (c_1,\dots,c_r)$ of elements, the input string $\langle B, \bar c\rangle \in \{0,1\}^*$ is
--   $$
--   1^n\,0\;\; T(R_1)\,T(R_2)\cdots T(R_k)\;\; e(c_1)\cdots e(c_r),
--   $$
--   where $T(R_i)$ is the $n^{a_i}$-bit table of $R_i$ (the tuples of $D^{a_i}$ in lexicographic order, bit $1$ iff the tuple is in $R_i$) and $e(c)$ is the $n$-bit vector with a single $1$ at position $c$.
--
--   For an $r$-ary query $Q$, $\mathrm{Graph}(Q) = \{\langle B,\bar c\rangle \mid B \models Q(\bar c)\}$ is the language of encodings of the pairs in the answer of $Q$.
--
--   This is the input format through which polynomial-time computability of queries is defined.
--
--   **Formalization Note** The page writes "some binary representation for $c_1\dots c_r$"; here each $c_i$ is written one-hot, which is a binary string of length $n$ (positional binary gives the same class P: milestone `encoding_robust`). The prefix $1^n0$ takes the place of the table of $\le$, which $n$ determines; it keeps the domain size in the input also when no relation has positive arity.
-- source:
--   N. Immerman, Relational Queries Computable in Polynomial Time (Extended Abstract), Proc. 14th ACM STOC, 1982, pp.147–152, doi:10.1145/800070.802187, §2 p.149 (Graph(φ) = {⟨B,c⟩ | B ⊨ φ(c)}), proof of Theorem 1 p.149 (the input: bit tables for R1, …, Rs, then a binary representation for c1 … cr) (PDF p.3)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_RelQueryPTime_Syntax

namespace RelQueryPTime

/-- The `a`-tuples over `Fin n` in lexicographic order. -/
def tuples (n : ℕ) : (a : ℕ) → List (Fin a → Fin n)
  | 0 => [Fin.elim0]
  | a + 1 => (List.finRange n).flatMap fun d => (tuples n a).map (Fin.cons d)

/-- The `n^{a_i}`-bit table of the relation `R_i` of `B`, tuples in lexicographic order
(Immerman, STOC 1982, proof of Theorem 1, p.149). -/
def Database.table {σ : Schema} {n : ℕ} (B : Database σ n) (i : Fin σ.k) : List Bool :=
  (tuples n (σ.arity i)).map (B.rel i)

/-- The input string `⟨B, c⟩` (Immerman, STOC 1982, proof of Theorem 1, p.149): the prefix
`1ⁿ0`, then the bit tables of `R₁, …, R_k`, then, for each `c_i`, the `n`-bit vector with a single
`1` at position `c_i`.

**Formalization Note** The page writes "some binary representation for `c₁ … c_r`"; here each
`c_i` is written one-hot (a binary string of length `n`). The prefix `1ⁿ0` takes the place of the
table of `≤`, which `n` determines, and makes the size of the database part of the input also
when no relation has positive arity. -/
def enc {σ : Schema} {n r : ℕ} (B : Database σ n) (c : Fin r → Fin n) : List Bool :=
  List.replicate n true ++ false ::
    ((List.finRange σ.k).flatMap B.table ++
      (List.finRange r).flatMap fun i => (List.finRange n).map fun d => decide (d = c i))

/-- `Graph(Q) = {⟨B, c⟩ | B ⊨ Q(c)}` (Immerman, STOC 1982, §2, p.149), as a language over
`{0, 1}`: the encodings of the pairs in the answer of `Q`. -/
def Graph {σ : Schema} {r : ℕ} (Q : Query σ r) : CookPvsNP.Lang Bool :=
  {w | ∃ (n : ℕ) (B : Database σ n) (c : Fin r → Fin n), Q n B c ∧ w = enc B c}

end RelQueryPTime


