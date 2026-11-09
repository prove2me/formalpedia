-- Prove2me | Definitions.Def_LZ78Rank_LZ78
-- name    : LZ78Rank_LZ78
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:44:41.003247+00:00
-- url     : https://prove2.me/theorems/eac968c2-c6bb-4f9f-8de0-7569e3baeb33
-- title:
--   The LZ78 factorization $T=f_1\cdots f_{z}$, $z_{78}(T)$ and the LZ78 representation
-- statement:
--   The **LZ78 factorization** (Definition 2.10) of a string $T$ is $T=f_1f_2\cdots f_k$ where, with $f_0=\varepsilon$, each phrase $f_i$ is the longest prefix of the not yet parsed suffix such that $f_i=f_j\cdot c$ for some $j\in[0\,.\,.\,i)$ and some symbol $c$. The number of phrases is $z_{78}(T)=k$. The phrases $f_1,\dots,f_{k-1}$ are distinct; the last one may repeat an earlier phrase (for $T=11$ the factorization is $1\cdot 1$).
--
--   The **LZ78 representation** (Definition 2.11) is the sequence of pairs $((p_1,c_1),\dots,(p_k,c_k))$ with $p_i\in[0\,.\,.\,i)$ and $f_i=f_{p_i}\cdot c_i$ for every $i\in[1\,.\,.\,k]$. It is unique (Remark 2.12). Its machine layout is the word sequence $k,p_1,c_1,\dots,p_k,c_k$.
--
--   For example (Example 2.14), $T=121323131$ factors as $1\cdot2\cdot13\cdot23\cdot131$, $z_{78}(T)=5$, with representation $((0,1),(0,2),(1,3),(2,3),(3,1))$.
--
--   **Formalization Note** The factorization is computed greedily: from the unparsed suffix $r\neq\varepsilon$ the next phrase is the longest nonempty prefix $u$ of $r$ whose last symbol removed is $\varepsilon$ or an earlier phrase. A prefix of length $1$ always qualifies, so the recursion consumes a symbol per phrase. Phrases are 1-based with $f_0=\varepsilon$.
-- source:
--   De–Kempa, Near-Optimal Compressed Algorithms and Data Structures by Eliminating Recursive Substructures, STOC 2027 submission (manuscript sha256 db4050af4e62ca74150f041d554ea7b206351a0c4ce7a37cb017488d6330ec6d), Definitions 2.10 and 2.11 and Remark 2.12, pp.11–12 (PDF pp.11–12)

import Mathlib

set_option autoImplicit false

namespace LZ78Rank

/-!
# The LZ78 factorization and the LZ78 representation

De–Kempa, *Near-Optimal Compressed Algorithms and Data Structures by Eliminating Recursive
Substructures*, STOC 2027 submission (manuscript sha256 db4050af4e62…330ec6d), Definitions 2.10
and 2.11 and Remark 2.12, pp.11–12 (= PDF pp.11–12).

Definition 2.10: "letting f₀ = ε, for every i ∈ [1 . . k], after f₁ ⋯ f_{i−1} has been parsed,
fᵢ is the longest prefix of the remaining suffix fᵢfᵢ₊₁ ⋯ f_k such that there exists
j ∈ [0 . . i) satisfying fᵢ = f_j · c for some symbol c."

**Formalization Note.**
* `lz78 T` computes this greedy factorization: from the unparsed suffix `r ≠ []` the next phrase
  is the longest nonempty prefix `u` of `r` whose last symbol removed (`u.dropLast`) is `ε` or an
  earlier phrase. A prefix of length 1 always qualifies, so every step consumes a symbol and the
  fuel `|T|` suffices. The last phrase may repeat an earlier one (Remark 2.12; `T = 11` gives
  `1 · 1`).
* Phrases are 1-based: `phrase T i = fᵢ` for `i ∈ [1 . . z₇₈(T)]` and `phrase T 0 = f₀ = ε`.
* The representation `((p₁, c₁), …, (p_k, c_k))` is a `List (ℕ × ℕ)`; its machine layout is
  `encRep`: the number `k` of pairs followed by `p₁, c₁, …, p_k, c_k`.
-/

/-- The length of the next LZ78 phrase of the unparsed suffix `r`, given the phrases `dict`
parsed so far: the largest `k ∈ [1 . . |r|]` such that `r[1 . . k]` with its last symbol removed
is `ε` or a phrase of `dict` (`0` if `r = []`). -/
def lz78NextLen (dict : List (List ℕ)) (r : List ℕ) : ℕ :=
  ((List.range (r.length + 1)).filter
    (fun k => decide (1 ≤ k ∧ (r.take k).dropLast ∈ ([] :: dict)))).foldr max 0

/-- The greedy LZ78 parse of `r` with fuel, continuing after the phrases `dict`. -/
def lz78Aux : ℕ → List (List ℕ) → List ℕ → List (List ℕ)
  | 0, _, _ => []
  | fuel + 1, dict, r =>
    if r = [] then []
    else
      (r.take (max 1 (lz78NextLen dict r))) ::
        lz78Aux fuel (dict ++ [r.take (max 1 (lz78NextLen dict r))])
          (r.drop (max 1 (lz78NextLen dict r)))

/-- **The LZ78 factorization** `T = f₁ f₂ ⋯ f_k` (Definition 2.10, p.11), as the list of phrases
`[f₁, …, f_k]`. -/
def lz78 (T : List ℕ) : List (List ℕ) := lz78Aux T.length [] T

/-- `z₇₈(T)`, the number of phrases of the LZ78 factorization (Definition 2.10, p.11). -/
def z78 (T : List ℕ) : ℕ := (lz78 T).length

/-- The phrase `fᵢ` of the LZ78 factorization (1-based), with `f₀ = ε` (Definition 2.10). -/
def phrase (T : List ℕ) (i : ℕ) : List ℕ := ([] :: lz78 T).getD i []

/-- **The LZ78 representation** (Definition 2.11, pp.11–12): `reps = ((p₁, c₁), …, (p_k, c_k))`
with `k = z₇₈(T)` and, for every `i ∈ [1 . . k]`, `pᵢ ∈ [0 . . i)` and `fᵢ = f_{pᵢ} · cᵢ`.
By Remark 2.12 it is unique. -/
def IsLZ78Rep (T : List ℕ) (reps : List (ℕ × ℕ)) : Prop :=
  reps.length = z78 T ∧
    ∀ i : ℕ, 1 ≤ i → i ≤ z78 T →
      (reps.getD (i - 1) (0, 0)).1 < i ∧
        phrase T i = phrase T (reps.getD (i - 1) (0, 0)).1 ++ [(reps.getD (i - 1) (0, 0)).2]

/-- The machine layout of an LZ78 representation: `k, p₁, c₁, p₂, c₂, …, p_k, c_k`. -/
def encRep (reps : List (ℕ × ℕ)) : List ℕ :=
  reps.length :: reps.flatMap (fun p => [p.1, p.2])

end LZ78Rank


