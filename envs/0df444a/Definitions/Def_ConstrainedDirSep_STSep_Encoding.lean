-- Prove2me | Definitions.Def_ConstrainedDirSep_STSep_Encoding
-- name    : ConstrainedDirSep_STSep_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:05:46.361135+00:00
-- url     : https://prove2.me/theorems/eb27e201-edd6-4437-aea1-46f104f92795
-- title:
--   Input and output words, the H-membership oracle and admissible queries
-- statement:
--   Words are lists of bits. A natural number $k$ is written **self-delimiting in binary** as $\mathrm{enc}(k)$: each binary digit (least significant first) preceded by a $1$, then a final $0$. A digraph $F$ on $\{0,\dots,m-1\}$ is written as $\mathrm{enc}(m)$ followed by its $m^2$ adjacency bits, row by row.
--
--   - **Instance word** of H-Directed $s$–$t$ Separator: the digraph $D$ on $n$ vertices, then $\mathrm{enc}(s)$, $\mathrm{enc}(t)$, $\mathrm{enc}(k)$.
--   - **Weighted instance word**: the instance word, then $\mathrm{enc}(w(v))$ for every $v \notin \{s,t\}$ in vertex order (binary weights).
--   - **Output words**: "none exists" is the single bit $0$; a vertex set $S$ is the bit $1$ followed by its $n$ membership bits.
--   - **The $\mathcal H$-membership oracle** answers $1$ on a query word that encodes a loopless digraph $F \in \mathcal H$, and $0$ on every other word.
--   - A query is **admissible for budget $k$** if it encodes a loopless digraph with at most $k$ vertices.
--
--   The helpers `charBits` (membership bits of a set along a list) and `rangeOne d` (the list $1,\dots,d$, i.e. $[d]$) write the finite sets of the Chain CSP and representation layers explicitly.
--
--   **Formalization Note.** The oracle is the only access an algorithm has to $\mathcal H$; together with a bound on the number of calls and on query size it replaces the paper's term $2^{O(k^2)}\tau_{\mathcal H}(k)$, where $\tau_{\mathcal H}(k)$ is the running time of a membership test on adjacency matrices of digraphs with at most $k$ vertices.
-- source:
--   Olkowski, Ramanujan, Constrained Directed Separation: Algorithms and Classifications, STOC 2027 submission (manuscript sha256 4dd06c29…), p. 2 (PDF 5), §1.1.1 (τ_H, binary weights, n); p. 15 (PDF 18), §4 (explicit encoding)

import Mathlib
import Definitions.Def_ConstrainedDirSep_STSep_Separator

set_option autoImplicit false

namespace ConstrainedDirSep.STSep

/-- **Self-delimiting binary encoding of a natural number.** Olkowski, Ramanujan, *Constrained
Directed Separation*, STOC 2027 submission (manuscript sha256 4dd06c29…), §1.1.1, p. 2 (PDF 5):
"All vertex weights are nonnegative integers encoded in binary."

`encNat k` lists the binary digits of `k` (least significant first, `Nat.bits`), each preceded by
the flag `true`, and ends with `false`; so `encNat 0 = [false]` and the word has length
`2·⌈log₂(k+1)⌉ + 1`. -/
def encNat (k : ℕ) : List Bool :=
  (k.bits.flatMap fun b => [true, b]) ++ [false]

open Classical in
/-- **Adjacency matrix of a digraph on `Fin n`**, row by row: entry `(u, v)` is `true` iff `uv` is
an arc. §1.1.1, p. 2 (PDF 5): τ_H is measured "on digraphs … represented by adjacency matrices". -/
noncomputable def adjBits {n : ℕ} (D : Digraph (Fin n)) : List Bool :=
  (List.finRange n).flatMap fun u => (List.finRange n).map fun v => decide (D.Adj u v)

open Classical in
/-- **Characteristic bit vector** of a predicate `P` along a list `l`: the bits `[P a]` for `a ∈ l`,
in order. Used to write a finite set "explicitly" (§4, p. 15, PDF 18: "All sets are explicitly
encoded without repetitions") as its membership bits over a known finite range. -/
noncomputable def charBits {α : Type*} (P : α → Prop) (l : List α) : List Bool :=
  l.map fun a => decide (P a)

/-- **The integers `1, …, d`**, i.e. the paper's domain `[d]` (§3, p. 14, PDF 17: "[m] = {1, …, m},
and let [0] = ∅"), as a list in increasing order. -/
def rangeOne (d : ℕ) : List ℕ := List.range' 1 d

/-- **Encoding of a digraph on `Fin m`**: `encNat m` followed by its `m²` adjacency bits. This is
the word the algorithm writes on its query stack to ask the H-membership oracle about a digraph,
and the first block of an input instance. -/
noncomputable def encDigraph (m : ℕ) (F : Digraph (Fin m)) : List Bool :=
  encNat m ++ adjBits F

/-- **Input word of an instance of H-Directed s–t Separator** (§1.1.1, p. 2, PDF 5): the digraph
`D` on `Fin n` by adjacency matrix, then the terminals `s`, `t` (as indices) and the budget `k`.
Nothing else (in particular nothing about H) is part of the input. -/
noncomputable def encInstance {n : ℕ} (D : Digraph (Fin n)) (s t : Fin n) (k : ℕ) : List Bool :=
  encDigraph n D ++ encNat s.val ++ encNat t.val ++ encNat k

/-- **Input word of a weighted instance** (§5.2.2, p. 27, PDF 30): the unweighted input word,
followed by the binary weight `w(v)` of every nonterminal `v ∈ V(D) \ {s, t}`, in vertex order.
The weights of `s` and `t` are not part of the input (the paper's `w` is defined on
`V(D) \ {s, t}` only). -/
noncomputable def encWInstance {n : ℕ} (D : Digraph (Fin n)) (s t : Fin n) (k : ℕ)
    (w : Fin n → ℕ) : List Bool :=
  encInstance D s t k ++
    (List.finRange n).flatMap fun v => if v = s ∨ v = t then [] else encNat (w v)

/-- **The output word "none exists"**: the single bit `false`. -/
def encNone : List Bool := [false]

/-- **The output word of a vertex set `S ⊆ Fin n`**: the bit `true` followed by the `n` membership
bits of `S` in vertex order. -/
def encSet {n : ℕ} (S : Finset (Fin n)) : List Bool :=
  true :: (List.finRange n).map fun v => decide (v ∈ S)

open Classical in
/-- **The H-membership oracle.** §1.1.1, p. 2 (PDF 5): "We use a fixed algorithm to test
membership in H." On a query word that encodes a loopless digraph `F` on `Fin m` (`encDigraph m F`)
the oracle answers `[true]` if `F ∈ H` and `[false]` otherwise; on any other word it answers
`[false]`.

**Formalization Note.** The algorithm accesses H only through this oracle; its running time
τ_H(k) is accounted for by the call count and the query-size predicate `IsSmallDigraphQuery`. -/
noncomputable def HOracle (H : DigraphClass) (q : List Bool) : List Bool :=
  if ∃ (m : ℕ) (F : Digraph (Fin m)), Loopless F ∧ q = encDigraph m F ∧ H m F then [true]
  else [false]

/-- **A query about a digraph with at most `k` vertices.** §1.1.1, p. 2 (PDF 5): τ_H(k) is the
worst-case running time of the membership test "on digraphs with at most k vertices, represented
by adjacency matrices". A query word `q` is admissible if it encodes a loopless digraph on `Fin m`
with `m ≤ k`. -/
def IsSmallDigraphQuery (k : ℕ) (q : List Bool) : Prop :=
  ∃ m ≤ k, ∃ F : Digraph (Fin m), Loopless F ∧ q = encDigraph m F

end ConstrainedDirSep.STSep


