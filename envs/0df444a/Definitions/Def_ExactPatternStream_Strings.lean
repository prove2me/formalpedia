-- Prove2me | Definitions.Def_ExactPatternStream_Strings
-- name    : ExactPatternStream_Strings
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:02:09.501431+00:00
-- url     : https://prove2.me/theorems/370d4216-bdf5-4b48-84e9-c2e812ad23fe
-- title:
--   §3 — substrings, $\mathrm{Occ}(P,T)$, erase and expand
-- statement:
--   Strings are $0$-indexed. The substring $S[i\,.\,.\,j)$ lists the characters of $S$ whose indices lie in $[i\,.\,.\,j)\cap[0\,.\,.\,|S|)$, so it is cut to the valid range. For strings $P,T$,
--   $$\mathrm{Occ}(P,T)=\{a\in[0\,.\,.\,|T|-|P|]:T[a\,.\,.\,a+|P|)=P\}.$$
--   Definition 3.2: $\mathrm{erase}(S,c)$ removes all occurrences of the symbol $c$ from $S$. Definition 3.3: for $\rho:[0\,.\,.\,s]\to[0\,.\,.\,t]$ strictly increasing with $\rho(s)=t$ and $|S|=s$, the string $\mathrm{expand}(S,\rho,c)$ has length $t$; its entry $i$ is $S[j]$ if $i=\rho(j)$ for some $j<s$, and $c$ otherwise.
--
--   These are the string conventions of the whole mission; the truncation matters in Algorithm 2 and Lemma 8.5.
--
--   **Formalization Note** Strings are `List`s and `Occ` is a `Finset ℕ`. If $|P|>|T|$ the truncated slice is shorter than $P$, so the set is empty.
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), §3, pp.5–6 (PDF 6–7), Definitions 3.2, 3.3

import Mathlib

namespace ExactPatternStream

/-! # Strings, occurrences, `erase`, `expand`

Gawrychowski, Janczewski, Jin, Nelson, *An Improved Streaming Algorithm for Exact Pattern Matching*
(preprint, STOC 2027 submission, sha256 351218cb…), §3, pp.5–6 (PDF 6–7), Definitions 3.2, 3.3.

**Formalization Note.** Strings are 0-indexed `List`s. `slice S i j` is the paper's `S[i . . j)`, which
"lists the characters whose indices lie in `[i . . j) ∩ [0 . . |S|)`" (p.6), so it truncates and never
fails. `S[i . . j]` is `slice S i (j + 1)`. `occ P T` is a `Finset ℕ`; when `|P| > |T|` the truncating
slice is shorter than `P`, so the set is empty, and the natural-number subtraction is harmless. -/

variable {α : Type*}

/-- `S[i . . j)`, truncated to the valid positions of `S` (p.6). -/
def slice (S : List α) (i j : ℕ) : List α := (S.drop i).take (j - i)

/-- `Occ(P, T) = {a ∈ [0 . . |T| - |P|] : T[a . . a + |P|) = P}` (p.6). -/
def occ [DecidableEq α] (P T : List α) : Finset ℕ :=
  (Finset.range (T.length - P.length + 1)).filter fun a => slice T a (a + P.length) = P

/-- Definition 3.2: `erase(S, c)` removes all occurrences of `c` from `S`. -/
def erase [DecidableEq α] (S : List α) (c : α) : List α := S.filter (· ≠ c)

/-- Definition 3.3: `expand(S, ρ, c)` has length `t = ρ(s)`, `s = |S|`; its entry `i` is `S[j]` if
`i = ρ(j)` for some `j ∈ [0 . . s)`, and `c` otherwise. For `ρ` strictly increasing the `j` is unique. -/
def expand (S : List α) (ρ : ℕ → ℕ) (c : α) : List α :=
  (List.range (ρ S.length)).map fun i =>
    match (List.range S.length).find? (fun j => ρ j == i) with
    | some j => S.getD j c
    | none => c

end ExactPatternStream


