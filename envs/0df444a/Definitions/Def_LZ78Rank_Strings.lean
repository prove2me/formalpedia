-- Prove2me | Definitions.Def_LZ78Rank_Strings
-- name    : LZ78Rank_Strings
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:44:37.545206+00:00
-- url     : https://prove2.me/theorems/bdf4feb9-0d6c-4727-b685-fff16fed6887
-- title:
--   Strings over $\{1,\dots,\sigma\}$, dictionaries, concatenations and $\mathrm{rank}_T(i,c)$
-- statement:
--   A **string** over the alphabet $\{1,\dots,\sigma\}$ is a finite sequence $T=T[1]\cdots T[|T|]$ of symbols in $[1\,.\,.\,\sigma]$; an index sequence $X\in[1\,.\,.\,n]^m$ is a string over $[1\,.\,.\,n]$. A **dictionary** $\mathcal D=(D_1,\dots,D_n)$ is a list of strings, duplicates allowed, and $\mathcal D\subseteq\{1,\dots,\sigma\}^+$ means every $D_i$ is nonempty and over $[1\,.\,.\,\sigma]$. This module defines:
--
--   1. the **rank** (Definition 2.1): for $i\in[0\,.\,.\,|T|]$ and a symbol $c$,
--   $$\mathrm{rank}_T(i,c)=\bigl|\{\,j\in[1\,.\,.\,i] : T[j]=c\,\}\bigr| ;$$
--   2. the concatenation $\bigodot_{j=1}^{m} D_{x_j}=D_{x_1}D_{x_2}\cdots D_{x_m}$ of the dictionary strings named by $X=(x_1,\dots,x_m)$;
--   3. the concatenation of prefixes $\bigodot_{j=1}^{\ell} s_{x_j}[1\,.\,.\,y_j]$ named by pairs $(x_j,y_j)$ (Lemma 3.3);
--   4. the **total size** $\sum_i |D_i|$;
--   5. **dictionary inclusion** $\mathcal D_1\subseteq\mathcal D_2$ (p.9): every distinct string occurring $c$ times in $\mathcal D_1$ occurs at least $c$ times in $\mathcal D_2$, i.e. inclusion of multisets.
--
--   These are the objects in which every statement of the mission is phrased.
--
--   **Formalization Note** Strings are `List ℕ` and dictionaries `List (List ℕ)`, with 1-based symbols and indices ($D_x$ is entry $x-1$ of the list). `List.take` caps an index above $|T|$ at $|T|$, so every statement restricts the rank index $i$ to $[0\,.\,.\,|T|]$ itself.
-- source:
--   De–Kempa, Near-Optimal Compressed Algorithms and Data Structures by Eliminating Recursive Substructures, STOC 2027 submission (manuscript sha256 db4050af4e62ca74150f041d554ea7b206351a0c4ce7a37cb017488d6330ec6d), Section 2.1.1, p.9 (PDF p.9), and Definition 2.1, p.10 (PDF p.10)

import Mathlib

set_option autoImplicit false

namespace LZ78Rank

/-!
# Strings, dictionaries and rank

De–Kempa, *Near-Optimal Compressed Algorithms and Data Structures by Eliminating Recursive
Substructures*, STOC 2027 submission (manuscript sha256 db4050af4e62…330ec6d), Section 2.1.1
(strings and dictionaries, p.9 = PDF p.9) and Definition 2.1 (rank, p.10 = PDF p.10).

**Formalization Note.**
* A string over the alphabet `{1, …, σ}` is a `List ℕ` all of whose entries lie in `[1 . . σ]`
  (`InAlphabet σ`). Symbols are 1-based, as in the paper, so a symbol is literally the machine word
  that stores it. A sequence of indices `X ∈ [1 . . n]^m` is likewise `InAlphabet n X`.
* A dictionary `D = (D₁, …, D_k)` is a `List (List ℕ)` (duplicates allowed); `D_x` is
  `D.getD (x - 1) []` (1-based). `D ⊆ {1, …, σ}⁺` is `DictOver σ D`.
* Positions are 1-based: `T[1 . . i]` is `T.take i`.
-/

/-- `T ∈ {1, …, σ}*`: every symbol of `T` lies in `[1 . . σ]` (p.9). Also used for index
sequences `X ∈ [1 . . n]^m`. -/
def InAlphabet (σ : ℕ) (T : List ℕ) : Prop := ∀ x ∈ T, 1 ≤ x ∧ x ≤ σ

/-- **Rank** (Definition 2.1, p.10): `rank_T(i, c) = |{j ∈ [1 . . i] : T[j] = c}|`, the number of
occurrences of `c` among the first `i` symbols of `T`.

**Formalization Note** The paper defines it for `i ∈ [0 . . |T|]`; `List.take` silently caps
`i` at `|T|`, so every statement restricts `i` itself. -/
def rank (T : List ℕ) (i c : ℕ) : ℕ := (T.take i).count c

/-- `D ⊆ {1, …, σ}⁺` (p.9): every string of the dictionary is nonempty and over `[1 . . σ]`. -/
def DictOver (σ : ℕ) (D : List (List ℕ)) : Prop := ∀ d ∈ D, d ≠ [] ∧ InAlphabet σ d

/-- The concatenation `⊙_{j=1,…,m} D_{x_j}` of the dictionary strings named by the 1-based index
sequence `X = (x₁, …, x_m)` (Sections 3–4). -/
def concatDict (D : List (List ℕ)) (X : List ℕ) : List ℕ :=
  (X.map fun x => D.getD (x - 1) []).flatten

/-- The concatenation `⊙_{j=1,…,ℓ} s_{x_j}[1 . . y_j]` of prefixes of dictionary strings named by
the 1-based pairs `(x_j, y_j)` (Lemma 3.3, p.14). -/
def prefixConcat (S : List (List ℕ)) (ps : List (ℕ × ℕ)) : List ℕ :=
  (ps.map fun p => (S.getD (p.1 - 1) []).take p.2).flatten

/-- The total size `Σ_i |D_i|` of a dictionary. -/
def totalSize (D : List (List ℕ)) : ℕ := (D.map List.length).sum

/-- Dictionary inclusion (p.9): `D₁ ⊆ D₂` "when every distinct string `w ∈ D₁` with `c` copies
also appears in `D₂` with at least `c` many copies", i.e. inclusion of multisets. -/
def DictSubset (D₁ D₂ : List (List ℕ)) : Prop :=
  (D₁ : Multiset (List ℕ)) ≤ (D₂ : Multiset (List ℕ))

end LZ78Rank


