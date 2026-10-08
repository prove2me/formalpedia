-- Prove2me | Definitions.Def_collatzFrontierWordWindows
-- name    : collatzFrontierWordWindows
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-04T17:35:59.879284+00:00
-- url     : https://prove2.me/theorems/4009e76c-fb68-44b7-8990-e0b46bb1a1c6
-- title:
--   Cyclic valuation windows for Syracuse orbits and words
-- statement:
--   Let $T(n)=\operatorname{oddpart}(3n+1)$ be the Syracuse map and $v_2$ the exponent of two. For a natural number $m$ (thought of as a point on a Syracuse orbit) and $k,i\in\mathbb N$, the *orbit valuation window* $\mathrm{orbitValuationWindow}(m,k,i)$ is the length-$k$ sequence of consecutive valuations starting at step $i$:
--
--   $$\bigl(v_2(3\,T^{i}(m)+1),\,v_2(3\,T^{i+1}(m)+1),\,\dots,\,v_2(3\,T^{i+k-1}(m)+1)\bigr).$$
--
--   For a finite list $w=(a_0,\dots,a_{p-1})$ of natural numbers (a candidate valuation word, $p=\operatorname{length}(w)$), the *word valuation window* $\mathrm{wordValuationWindow}(w,k,i)$ is the length-$k$ cyclic block of entries of $w$ starting at index $i$, obtained by rotating $w$ left by $i$ and reading off its first $k$ entries (indices taken modulo $p$, following Lean's `List.rotate`).
--
--   Finally, $\mathrm{wordWindowCount}(w,k)$ counts how many *distinct* length-$k$ windows $w$ exhibits as the start index $i$ ranges over $\{0,\dots,p-1\}$:
--
--   $$N_k(w) = \#\{\,\mathrm{wordValuationWindow}(w,k,i) : 0\le i<p\,\}.$$
--
--   These three definitions set up a finite combinatorial complexity measure on a word (or on a realized orbit): $N_k(w)$ is small exactly when the word's length-$k$ cyclic substrings repeat often. This measure is the basis of a packing argument used to bound how long a Syracuse cycle with few distinct windows can be, relative to the spread of its states — see the companion theorems `CollatzFrontier.least_cycle_window_capacity` (orbit form) and `CollatzFrontier.primitive_word_nondivisibility_of_window_capacity` (word form).
--
--   **Formalization Note.** `orbitValuationWindow` needs the platform's `syracuseStep` (`Definitions.Def_syracuseStep`); `wordValuationWindow` and `wordWindowCount` operate purely on lists and do not. All three are plain, non-recursive, sorry-free definitions.
-- source:
--   Original definitions of this contribution, extracted from the private repository collatz-frontier, branch research/window-complexity-20261002, commit a3a13a7cb543ccbc29d83fe91aaa68f59fa13874, file lean/CollatzFrontier/WindowComplexity.lean (declarations orbitValuationWindow, wordValuationWindow, wordWindowCount). Depends on the platform Syracuse step Definitions.Def_syracuseStep.

import Mathlib.Data.List.Rotate
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Fin
import Definitions.Def_syracuseStep

set_option autoImplicit false

/-
  Cyclic valuation windows for a Syracuse orbit and for an abstract word.

  These definitions support a finite packing/complexity obstruction: a
  length-`k` cyclic window records the next `k` dyadic valuations seen either
  along a realized Syracuse orbit (`orbitValuationWindow`) or directly inside
  a candidate word (`wordValuationWindow`), and `wordWindowCount` counts how
  many distinct such windows a word actually exhibits as the start index
  ranges over the whole word. Definitions only; no proofs beyond what is
  needed to state them.
-/

namespace CollatzFrontier

/-- The length-`k` window of 2-adic valuations of `3n+1` read along the
Syracuse orbit of `m`, starting at step `i` and wrapping forward through the
iteration (no cyclic reduction is applied here: this is a window on the
orbit itself, not yet on a realized cycle). -/
def orbitValuationWindow (m k i : ℕ) : Fin k → ℕ :=
  fun j => (3 * syracuseStep^[i + j.val] m + 1).factorization 2

/-- The length-`k` cyclic window of entries of the word `w`, starting at
index `i` and wrapping around via `List.rotate`. -/
def wordValuationWindow (w : List ℕ) (k i : ℕ) : Fin k → ℕ :=
  fun j => (w.rotate (i + j.val)).head!

/-- The number of distinct length-`k` cyclic windows exhibited by `w`, i.e.
the number of distinct values of `wordValuationWindow w k i` as the start
index `i` ranges over `Fin w.length`. This is the word's window complexity
at scale `k`: a word with small `wordWindowCount` relative to its length
carries little information per window and is correspondingly easy to pack
into a short interval of residues. -/
def wordWindowCount (w : List ℕ) (k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin w.length)).image (fun i => wordValuationWindow w k i.val)).card

end CollatzFrontier


