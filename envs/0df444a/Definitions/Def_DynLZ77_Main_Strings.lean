-- Prove2me | Definitions.Def_DynLZ77_Main_Strings
-- name    : DynLZ77_Main_Strings
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:20:12.033912+00:00
-- url     : https://prove2.me/theorems/18b64304-e0d4-46c5-8fda-aa562b2fd185
-- title:
--   Strings, LCP and LCS, the longest previous factor LPF and LPF′, the LZ77 factorization, LZ-like parsings and edit operations
-- statement:
--   A **string** $S = S[1]S[2]\cdots S[n]$ over an alphabet $\Sigma$ is a finite sequence; positions are 1-based, $[i..j]=\{i,\dots,j\}$ (empty if $j<i$), $[i..j)=[i..j-1]$, and $S[i..j]$ is the substring $S[i]\cdots S[j]$ (empty if $j<i$). In Lean a string is a `List α` over an arbitrary type $\alpha$ with decidable equality; `charAt S i` is $S[i]$ (`none` outside $[1..n]$) and `sub S i j` is $S[i..j]$.
--
--   **Edit operations** on $S[1..n]$: a substitution $(i,\sigma)\in[n]\times\Sigma$ gives $S[1..i-1]\,\sigma\,S[i+1..n]$; a deletion $i\in[n]$ gives $S[1..i-1]\,S[i+1..n]$; an insertion $(i,\sigma)\in[n+1]\times\Sigma$ gives $S[1..i-1]\,\sigma\,S[i..n]$ (`Edit.Valid`, `Edit.apply`).
--
--   The **longest common prefix** $\mathrm{LCP}(S,T)=\max(\{\ell \mid S[1..\ell]=T[1..\ell]\}\cup\{0\})$ and the **longest common suffix** $\mathrm{LCS}(S,T)=\mathrm{LCP}(S^R,T^R)$. For positions $i,j$ of $S$:
--   $$\mathrm{LCP}_S(i,j)=\mathrm{LCP}(S[i..n],S[j..n]),\qquad \mathrm{LCS}_S(i,j)=\mathrm{LCS}(S[1..i],S[1..j]).$$
--
--   The **longest previous factor** of $i\in[n]$ is $\mathrm{LPF}_S(i)=\max_{j\in[1..i-1]}\mathrm{LCP}_S(i,j)$ (so $\mathrm{LPF}_S(1)=0$), the length of the longest prefix of $S[i..n]$ that also starts at an earlier position, and $\mathrm{LPF}'_S(i)=\max(\mathrm{LPF}_S(i),1)$.
--
--   The **LZ77 factorization** $\mathrm{LZ77}(S)$ is computed by a greedy left-to-right scan: start at $i=1$; while $i\ne n+1$, output the phrase $S[i..i+\mathrm{LPF}'_S(i))$ and move to $i+\mathrm{LPF}'_S(i)$. A phrase is either a single character with no earlier occurrence, or the longest prefix of the remaining suffix that starts earlier (the earlier occurrence may overlap the phrase). In Lean, `LZ77 S` is the list of phrases as position pairs $(a,b)$ (the phrase $S[a..b]$), and $z(S)=|\mathrm{LZ77}(S)|$; $z(\varepsilon)=0$.
--
--   A parsing $P=(F_1,\dots,F_k)$ of $X$ is **LZ-like** if $X=F_1\cdots F_k$ and every phrase $F_t=X[a..b]$ is a single character or has an occurrence in $X$ starting at a position strictly smaller than $a$ (overlap allowed). Phrases are nonempty (the phrases partition $X$). $|P|=k$.
--
--   These objects carry the paper's Lemma 4.5, Fact 4.6 and the whole of §8.
--
--   **Formalization Note.** The scan stops when $i$ leaves $[1..n]$; since $i+\mathrm{LPF}'_S(i)\le n+1$ for every $i\in[1..n]$, this is the paper's stop at $i=n+1$. `phraseStart P t` is the start position $1+|F_1|+\dots+|F_t|$ of the phrase with 0-based index $t$.
-- source:
--   Boneh, Fried, Golan, Kraus, Dynamic LZ77: No Space for Improvement, STOC 2027 submission (manuscript sha256 2a15e146…), p. 15 (PDF 17) strings, LCP, LCS; p. 16 (PDF 18) §4.1 edit operations; pp. 17-18 (PDF 19-20) §4.3 LPF, LPF′, LZ-like parsings, LZ77

import Mathlib

set_option autoImplicit false

namespace DynLZ77.Main

/-!
# Strings, LCP/LCS, the longest previous factor, LZ77 and LZ-like parsings, edit operations

Boneh, Fried, Golan, Kraus, *Dynamic LZ77: No Space for Improvement*, STOC 2027 submission
(manuscript sha256 2a15e146…): §4 Preliminaries, p. 15 (PDF 17) strings, LCP, LCS; §4.1, p. 16
(PDF 18) edit operations; §4.3, pp. 17-18 (PDF 19-20) LPF, LPF′, LZ-like parsings, LZ77.

**Formalization Note.**
* A string over an alphabet `α` is a `List α`; positions are **1-based** natural numbers, as in
  the paper. `charAt S i` is `S[i]` (`none` outside `[1..|S|]`), `sub S i j` is `S[i..j]`
  (empty when `j < i`).
* `lcp` is the paper's `LCP(S, T) = max({ℓ | S[1..ℓ] = T[1..ℓ]} ∪ {0})`;
  `lcpAt S i j = LCP(S[i..n], S[j..n])`, `lcsAt S i j = LCS(S[1..i], S[1..j]) = LCP` of the
  reversed prefixes.
* `lpf S i = max_{j ∈ [1..i−1]} LCP_S(i, j)` (`0` for `i = 1`, the maximum over the empty set);
  `lpf' S i = max(lpf S i, 1)`.
* `LZ77 S` is the paper's greedy scan as a function: the list of phrases `(a, b)` (the phrase
  `S[a..b]`, 1-based, inclusive), starting at `i = 1` and moving to `i + LPF′_S(i)`. The scan stops
  when `i` leaves `[1..|S|]`; since `i + LPF′_S(i) ≤ |S| + 1` for `i ∈ [1..|S|]`, this is exactly
  the paper's stop at `i = n + 1`. `LZ77 [] = []`, so `z = 0` for the empty string.
* An LZ-like parsing is a list of phrases (each a nonempty string, the parts of a partition)
  whose concatenation is `X`, each a single character or with an occurrence in `X` at an earlier
  starting position (overlap allowed).
-/

variable {α : Type}

/-- `S[i]`, 1-based; `none` when `i ∉ [1..|S|]`. -/
def charAt (S : List α) (i : ℕ) : Option α := if i = 0 then none else S[i - 1]?

/-- `S[i..j]` (1-based, inclusive): the `j + 1 − i` characters starting at position `i`
(the empty string when `j < i`). -/
def sub (S : List α) (i j : ℕ) : List α := (S.drop (i - 1)).take (j + 1 - i)

/-- An edit operation (§4.1, p. 16): substitution `(i, σ)`, deletion `i`, insertion `(i, σ)`. -/
inductive Edit (α : Type) where
  | subst (i : ℕ) (a : α)
  | del (i : ℕ)
  | ins (i : ℕ) (a : α)

/-- Validity of an edit on a string of length `n`: substitution and deletion need `i ∈ [n]`,
insertion needs `i ∈ [n + 1]`. -/
def Edit.Valid (n : ℕ) : Edit α → Prop
  | .subst i _ => 1 ≤ i ∧ i ≤ n
  | .del i => 1 ≤ i ∧ i ≤ n
  | .ins i _ => 1 ≤ i ∧ i ≤ n + 1

/-- The string after the edit: `S[1..i−1]·σ·S[i+1..n]`, `S[1..i−1]·S[i+1..n]`,
`S[1..i−1]·σ·S[i..n]`. -/
def Edit.apply (S : List α) : Edit α → List α
  | .subst i a => S.take (i - 1) ++ a :: S.drop i
  | .del i => S.take (i - 1) ++ S.drop i
  | .ins i a => S.take (i - 1) ++ a :: S.drop (i - 1)

variable [DecidableEq α]

/-- `LCP(S, T)`: the length of the longest common prefix. -/
def lcp : List α → List α → ℕ
  | a :: s, b :: t => if a = b then lcp s t + 1 else 0
  | _, _ => 0

/-- `LCP_S(i, j) = LCP(S[i..n], S[j..n])`. -/
def lcpAt (S : List α) (i j : ℕ) : ℕ := lcp (S.drop (i - 1)) (S.drop (j - 1))

/-- `LCS_S(i, j) = LCS(S[1..i], S[1..j]) = LCP(S[1..i]^R, S[1..j]^R)`. -/
def lcsAt (S : List α) (i j : ℕ) : ℕ := lcp (S.take i).reverse (S.take j).reverse

/-- `LPF_S(i) = max_{j < i} LCP_S(i, j)`, `j` ranging over the positions `[1..i−1]`. -/
def lpf (S : List α) (i : ℕ) : ℕ := (Finset.Ico 1 i).sup (fun j => lcpAt S i j)

/-- `LPF′_S(i) = max(LPF_S(i), 1)`. -/
def lpf' (S : List α) (i : ℕ) : ℕ := max (lpf S i) 1

/-- The greedy LZ77 scan from position `i`: phrases `(i, i + LPF′_S(i) − 1)`, then continue at
`i + LPF′_S(i)`, until `i` leaves `[1..|S|]`. -/
def lz77From (S : List α) (i : ℕ) : List (ℕ × ℕ) :=
  if 1 ≤ i ∧ i ≤ S.length then (i, i + lpf' S i - 1) :: lz77From S (i + lpf' S i) else []
termination_by S.length + 1 - i
decreasing_by
  have h1 : 1 ≤ lpf' S i := le_max_right _ _
  omega

/-- `LZ77(S)`, the LZ77 factorization (with self-references), as the list of its phrases
`(a, b)` = `S[a..b]`, in order. -/
def LZ77 (S : List α) : List (ℕ × ℕ) := lz77From S 1

/-- `z = |LZ77(S)|`, the number of phrases. -/
def z (S : List α) : ℕ := (LZ77 S).length

/-- The 1-based starting position of the phrase with 0-based index `t` of a parsing. -/
def phraseStart (P : List (List α)) (t : ℕ) : ℕ := ((P.take t).map List.length).sum + 1

/-- `P` is an LZ-like parsing of `X`: `X = F_1 ⋯ F_k`, every phrase nonempty, and every phrase
`F_t = X[a..b]` is a single character or occurs in `X` at a position `a' < a` (overlap allowed). -/
def IsLZLike (X : List α) (P : List (List α)) : Prop :=
  P.flatten = X ∧ ∀ (t : ℕ) (ht : t < P.length), P[t] ≠ [] ∧
    (P[t].length = 1 ∨ ∃ a' : ℕ, 1 ≤ a' ∧ a' < phraseStart P t ∧
      (X.drop (a' - 1)).take P[t].length = P[t])

end DynLZ77.Main


