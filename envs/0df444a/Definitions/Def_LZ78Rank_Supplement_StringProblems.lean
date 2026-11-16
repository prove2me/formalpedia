-- Prove2me | Definitions.Def_LZ78Rank_Supplement_StringProblems
-- name    : LZ78Rank_Supplement_StringProblems
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:56:28.509086+00:00
-- url     : https://prove2.me/theorems/3bce1fdf-93b1-42d9-9312-a1292be1bc09
-- title:
--   Symbol occurrence $\mathrm{occurs}_T(b,e,c)$, Hamming distance, query batches and the class $z_{78}(S)=|S|^{1/2+o(1)}$
-- statement:
--   Strings are finite sequences over the positive integers, with 1-based positions $T[1],\dots,T[|T|]$.
--
--   1. **Symbol occurrence** (Definition 2.3). For $b,e\in[0\,.\,.\,|T|]$ and a symbol $c$,
--   $$\mathrm{occurs}_T(b,e,c)=\begin{cases}1&\text{if } T[i]=c \text{ for some } i\in(b\,.\,.\,e],\\0&\text{otherwise.}\end{cases}$$
--   For $b\ge e$ the range is empty and the value is $0$. For example, for $T=acaaba$, $\mathrm{occurs}_T(1,4,a)=1$ and $\mathrm{occurs}_T(1,4,b)=0$.
--   2. **Hamming distance** (Definition 5.3). For strings $T,P$ with $|T|=|P|$,
--   $$\mathrm{hamming}(T,P)=|\{i\in[1\,.\,.\,|T|] : T[i]\ne P[i]\}|.$$
--   3. **Query batches.** A batch of $q$ symbol occurrence queries $(b_1,e_1,c_1),\dots,(b_q,e_q,c_q)$ is given to a machine as the words $q,b_1,e_1,c_1,\dots,b_q,e_q,c_q$.
--   4. **The class $z_{78}(S)=\Theta(|S|^{1/2+o(1)})$** (Theorem 6.15). For a function $f:\mathbb N\to\mathbb R$, a string $S$ is in the class of $f$ when
--   $$|S|^{1/2-f(|S|)}\le z_{78}(S)\le |S|^{1/2+f(|S|)}.$$
--   When $f\to0$, this says that $\log z_{78}(S)/\log|S|\to 1/2$, which absorbs the constants of $\Theta$.
--
--   These are the problem-specific objects of Sections 5 and 6 of the paper. A string $P$ is a subsequence of $T$ when $P[j]=T[i_j]$ for some indices $1\le i_1<\dots<i_M\le |T|$ (Definition 5.1). That relation is Lean's `List.Sublist` and is not redefined here.
--
--   **Formalization Note** `occurs T b e c` tests membership of $c$ in the block `(T.drop b).take (e - b)`, which holds exactly the positions $b+1,\dots,e$. `hamming` counts the mismatches of `T.zip P`. Statements assume $|T|=|P|$; for unequal lengths the function counts mismatches on the common prefix.
-- source:
--   De–Kempa, Near-Optimal Compressed Algorithms and Data Structures by Eliminating Recursive Substructures, STOC 2027 submission (manuscript sha256 db4050af4e62ca74150f041d554ea7b206351a0c4ce7a37cb017488d6330ec6d), Definition 2.3, p.10 (PDF p.10); Definition 5.3, p.23 (PDF p.23); Theorems 6.8 and 6.15, pp.28 and 34 (PDF pp.28, 34)

import Mathlib
import Definitions.Def_LZ78Rank_LZ78

set_option autoImplicit false

namespace LZ78Rank.Supplement

open LZ78Rank

/-!
# Symbol occurrence, Hamming distance, batched queries and the class `Θ(n^{1/2+o(1)})`

De–Kempa, *Near-Optimal Compressed Algorithms and Data Structures by Eliminating Recursive
Substructures*, STOC 2027 submission (manuscript sha256 db4050af4e62…330ec6d):
Definition 2.3 (symbol occurrence, p.10 = PDF p.10), Definition 5.3 (Hamming distance, p.23 =
PDF p.23), Theorem 6.8 (batches of symbol occurrence queries, p.28 = PDF p.28) and Theorem 6.15
(the restriction `z₇₈(S) = Θ(|S|^{1/2+o(1)})`, p.34 = PDF p.34).

**Formalization Note.**
* Strings are `List ℕ` and positions are 1-based, as in the published `LZ78Rank.Strings`:
  `T[i]` is the entry of index `i − 1`.
* Subsequence (Definitions 5.1 and 6.15's "P is a subsequence of T") is Lean's `List.Sublist`
  (`P <+ T`); it needs no definition here.
-/

/-- **Symbol occurrence** (Definition 2.3, p.10): `occurs_T(b, e, c) = 1` if some `i ∈ (b . . e]`
has `T[i] = c`, and `0` otherwise. The 1-based positions `b + 1, …, e` are the list indices
`b, …, e − 1`, i.e. the block `(T.drop b).take (e − b)`; for `b ≥ e` the block is empty and the
value is `0`. The paper defines it for `b, e ∈ [0 . . |T|]`; statements restrict `b, e`. -/
def occurs (T : List ℕ) (b e c : ℕ) : ℕ := if c ∈ (T.drop b).take (e - b) then 1 else 0

/-- **Hamming distance** (Definition 5.3, p.23): `hamming(T, P) = |{i ∈ [1 . . |T|] : T[i] ≠ P[i]}|`
for `|T| = |P|`, the number of aligned positions where the two strings differ. (Statements
assume `|T| = |P|`; for unequal lengths this counts mismatches on the common prefix length.) -/
def hamming (T P : List ℕ) : ℕ := (T.zip P).countP (fun p => p.1 != p.2)

/-- The machine layout of a batch of `q` symbol occurrence queries `(b_j, e_j, c_j)`:
`q, b₁, e₁, c₁, …, b_q, e_q, c_q`. -/
def encQueries (qs : List (ℕ × ℕ × ℕ)) : List ℕ :=
  qs.length :: qs.flatMap (fun t => [t.1, t.2.1, t.2.2])

/-- The class of strings with `z₇₈(S) = Θ(|S|^{1/2+o(1)})` for a fixed `o(1)` function `f`
(Theorem 6.15, p.34): `|S|^{1/2 − f(|S|)} ≤ z₇₈(S) ≤ |S|^{1/2 + f(|S|)}` (real powers).
With `f → 0` this says `log z₇₈(S) / log |S| → 1/2`, which absorbs the constants of `Θ`. -/
def InClass (f : ℕ → ℝ) (S : List ℕ) : Prop :=
  (S.length : ℝ) ^ ((1 : ℝ) / 2 - f S.length) ≤ (z78 S : ℝ) ∧
    (z78 S : ℝ) ≤ (S.length : ℝ) ^ ((1 : ℝ) / 2 + f S.length)

end LZ78Rank.Supplement


