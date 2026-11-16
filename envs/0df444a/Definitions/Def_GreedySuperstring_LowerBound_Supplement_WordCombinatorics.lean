-- Prove2me | Definitions.Def_GreedySuperstring_LowerBound_Supplement_WordCombinatorics
-- name    : GreedySuperstring_LowerBound_Supplement_WordCombinatorics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:35:19.761858+00:00
-- url     : https://prove2.me/theorems/2013504b-a85a-46c2-b951-205f9c7f40e9
-- title:
--   Primitive words, cyclic equivalence, Lyndon words, and length-$m$ substring sets
-- statement:
--   Let $z$ be a finite word over an alphabet. The word $z$ is **primitive** if there are no word $v$ and integer $k\ge2$ with $z=v^k$; in particular the empty word is not primitive. Two words are **equivalent** if one is a cyclic rotation of the other.
--
--   Fix a linear order on the alphabet and order words lexicographically, a proper prefix being smaller. A **Lyndon word** is a nonempty word that is strictly smaller than each of its nonempty proper suffixes. The **least rotation** of a word $z$ is the lexicographically smallest of its cyclic rotations; for a nonempty primitive word this is the unique Lyndon word equivalent to it.
--
--   For a word $x$ and $m\ge0$, $\mathrm{Sub}_m(x)$ is the finite set of length-$m$ contiguous substrings of $x$, so $\mathrm{Sub}_0(x)=\{\varepsilon\}$ and $\mathrm{Sub}_m(x)=\emptyset$ for $m>|x|$. For a nonempty word $z$,
--
--   $$\mathrm{CSub}_m(z)=\{\text{length-}m\text{ substrings of }z^\infty\}.$$
--
--   These are the string-combinatorial notions of §2.6 used by Lemmas 2.3, 2.4 and 3.2 and the proof of Theorem 3.1.
--
--   **Formalization Note** $\mathrm{CSub}_m(z)$ is computed as the length-$m$ windows of $z^{m+2}$ starting at offsets $0,\dots,|z|-1$, which contain every window of $z^\infty$; for the empty word, where $z^\infty$ is undefined, it is empty. The least rotation of the empty word is the empty word. No Lyndon property of the least rotation is assumed.
-- source:
--   Nikolai Chukhin, Rishikesh Gajjala, Juha Harviainen, Alexander S. Kulikov, Ivan Mihajlin, Hiroki Shibata, Alexander V. Smal, The Greedy Superstring Conjecture Is False, STOC 2027 submission #316 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/316.pdf, SHA-256 84e171350ae4e20ed6899c32b480753dae49f7b418819656dfedbcac0f60e8fa, §2.6, printed pp.9–10 = PDF pp.9–10

import Mathlib

universe wc_u

namespace GreedySuperstring.LowerBound.Supplement

/-- §2.6, p.9: `z` is primitive iff there are no word `v` and integer `k ≥ 2`
with `z = v^k` (the `k`-fold concatenation of `v`). The empty word is `[]^2`,
so it is not primitive. -/
def IsPrimitive {α : Type wc_u} (z : List α) : Prop :=
  ∀ (v : List α) (k : ℕ), 2 ≤ k → z ≠ (List.replicate k v).flatten

/-- §2.6, p.9: two words are equivalent iff one is a cyclic rotation of the other
(Mathlib's `List.IsRotated`, `∃ n, z.rotate n = z'`). -/
def Equivalent {α : Type wc_u} (z z' : List α) : Prop :=
  z ~r z'

/-- §2.6, p.9: with a linear order on the alphabet and the lexicographic order on
words (a proper prefix is smaller), a Lyndon word is a nonempty word strictly smaller
than each of its nonempty proper suffixes. -/
def IsLyndon {α : Type wc_u} [LinearOrder α] (z : List α) : Prop :=
  z ≠ [] ∧ ∀ k : ℕ, 0 < k → k < z.length → z < z.drop k

/-- §2.6, p.10: `τ′`, the lexicographically least cyclic rotation of `z`. For a primitive
nonempty `z` this is the unique Lyndon word equivalent to `z`; no such property is assumed
here. For `z = []` it returns `[]`. -/
def leastRotation {α : Type wc_u} [LinearOrder α] (z : List α) : List α :=
  ((List.range z.length).map z.rotate).foldr min z

/-- §2.6, p.10: `Sub_m(x)`, the finite set of length-`m` contiguous substrings of `x`.
`Sub_0(x) = {[]}` and `Sub_m(x) = ∅` for `m > |x|`. -/
def subwords {α : Type wc_u} [DecidableEq α] (m : ℕ) (x : List α) : Finset (List α) :=
  ((List.range (x.length + 1 - m)).map (fun i => (x.drop i).take m)).toFinset

/-- §2.6, p.10: `CSub_m(z)`, the set of length-`m` substrings of `z^∞`. Every such
substring starts at an offset `i < |z|`; the `(m+2)`-fold power of `z` is long enough to
contain it, since `(m+2)|z| ≥ |z| + m` for nonempty `z`. For `z = []` (where `z^∞` is
undefined) it is `∅`. -/
def cyclicSubwords {α : Type wc_u} [DecidableEq α] (m : ℕ) (z : List α) : Finset (List α) :=
  ((List.range z.length).map
    (fun i => (((List.replicate (m + 2) z).flatten).drop i).take m)).toFinset

end GreedySuperstring.LowerBound.Supplement


