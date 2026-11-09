-- Prove2me | Definitions.Def_GreedySuperstring_LowerBound_WordModel
-- name    : GreedySuperstring_LowerBound_WordModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:27:27.735201+00:00
-- url     : https://prove2.me/theorems/79c1bd28-fb11-4569-a9dc-bc911a0508e3
-- title:
--   Proper overlap, overlap merge, and adjacent-prefix string notation
-- statement:
--   For finite words $s,t$ over an alphabet, their proper overlap $\operatorname{ov}(s,t)$ is the longest suffix of $s$ that is a prefix of $t$ and has length strictly smaller than both words. The empty overlap is allowed. Write $\operatorname{pref}(s,t)$ for the part of $s$ before the overlap. The overlap merge appends only the unshared suffix of $t$ to $s$:
--
--   $$\langle s,t\rangle=s\circ t[|\operatorname{ov}(s,t)|:].$$
--
--   For a nonempty list $t_1,\ldots,t_k$, the multiword notation is $\operatorname{pref}(t_1,t_2)\circ\cdots\circ\operatorname{pref}(t_{k-1},t_k)\circ t_k$. A set is substring-free when no distinct members contain one another as contiguous blocks. These are reusable primitives for all the mission's statements.
--
--   **Formalization Note** The alphabet is any type with decidable equality. The maximum ranges over a finite set of natural lengths strictly below both lengths. On an empty operand overlap is extended to the empty word; the source results use nonempty operands. The empty multiword list is also assigned the empty word. Neither extension changes any source instance.
-- source:
--   Nikolai Chukhin, Rishikesh Gajjala, Juha Harviainen, Alexander S. Kulikov, Ivan Mihajlin, Hiroki Shibata, Alexander V. Smal, The Greedy Superstring Conjecture Is False, STOC 2027 submission #316 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/316.pdf, §2.1–§2.2, printed pp.5–6 = PDF pp.5–6

import Mathlib

universe word_u

namespace GreedySuperstring.LowerBound

/-- Section 2.1, p.5: candidate lengths are strictly smaller than BOTH words.
For an empty operand the candidate set is empty and the extension returns zero. -/
def overlapLength {α : Type word_u} [DecidableEq α] (s t : List α) : ℕ :=
  ((Finset.range (min s.length t.length)).filter
    (fun n => s.drop (s.length - n) = t.take n)).sup id

/-- The actual overlap word, including proper self-overlaps. -/
def overlap {α : Type word_u} [DecidableEq α] (s t : List α) : List α :=
  t.take (overlapLength s t)

def pref {α : Type word_u} [DecidableEq α] (s t : List α) : List α :=
  s.take (s.length - overlapLength s t)

def merge {α : Type word_u} [DecidableEq α] (s t : List α) : List α :=
  s ++ t.drop (overlapLength s t)

/-- The paper's adjacent-prefix notation, not an arbitrary iterated binary merge. -/
def chainMerge {α : Type word_u} [DecidableEq α] : List (List α) → List α
  | [] => []
  | [t] => t
  | t :: v :: ts => pref t v ++ chainMerge (v :: ts)

/-- Distinct input words cannot contain each other as contiguous substrings. -/
def SubstringFree {α : Type word_u} (S : Finset (List α)) : Prop :=
  ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ¬ s <:+: t

end GreedySuperstring.LowerBound


