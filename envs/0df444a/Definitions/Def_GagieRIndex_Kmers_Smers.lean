-- Prove2me | Definitions.Def_GagieRIndex_Kmers_Smers
-- name    : GagieRIndex_Kmers_Smers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:24:05.116655+00:00
-- url     : https://prove2.me/theorems/1a092133-7445-46fc-b60f-6659c7b650a2
-- title:
--   Definition 5 and Lemma 9, pp. 16–17 — primary substrings and distinct s-mers
-- statement:
--   For a text $T[1..n]$, an $s$-mer is a length-$s$ substring $T[a..a+s-1]$ with $1\le a\le n-s+1$. The set of $s$-mers contains distinct strings, so repeated windows contribute only one element:
--   $$\mathcal S_s(T)=\{T[a..a+s-1]:1\le a\le n-s+1\}.$$
--
--   A valid substring $T[i..j]$ is primary when it contains at least one sampled text position $x$ with $i\le x\le j$. These notions are used by Lemmas 8 and 9 to relate BWT runs to substring complexity.
--
--   **Formalization Note** Each substring is a list of natural-number symbols. The finite set includes windows ending at the terminator and has no padding. The primary predicate includes $1\le i\le j\le n$ so that it denotes a genuine substring.
-- source:
--   Gagie, Navarro, Prezza, Fully-Functional Suffix Trees and Optimal Text Searching in BWT-runs Bounded Space, arXiv:1809.02792v2, p. 16, Definition 5; p. 17, Lemma 9

import Mathlib
import Definitions.Def_GagieRIndex_Locate_Core

namespace GagieRIndex.Kmers

/-- The distinct `s`-mers of `T[1..n]`: the substrings `T[a..a+s−1]`,
`1 ≤ a ≤ n − s + 1`, as a set of lists (Lemma 9, p. 17). -/
def smers (n : ℕ) (T : ℕ → ℕ) (s : ℕ) : Finset (List ℕ) :=
  (Finset.Icc 1 (n + 1 - s)).image (fun a => (List.range s).map (fun t => T (a + t)))

/-- A valid substring `T[i..j]` is primary when it contains a text position GagieRIndex.Locate.sampled at a BWT run
boundary (Definition 5, p. 16). -/
def IsPrimary (n : ℕ) (T SA : ℕ → ℕ) (i j : ℕ) : Prop :=
  1 ≤ i ∧ i ≤ j ∧ j ≤ n ∧ ∃ x ∈ GagieRIndex.Locate.sampled n T SA, i ≤ x ∧ x ≤ j

end GagieRIndex.Kmers


