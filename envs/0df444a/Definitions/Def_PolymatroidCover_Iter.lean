-- Prove2me | Definitions.Def_PolymatroidCover_Iter
-- name    : PolymatroidCover_Iter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:20:05.047758+00:00
-- url     : https://prove2.me/theorems/fafa1807-afc3-4b00-99d3-c8a875f418e1
-- title:
--   One while-loop iteration of Algorithm 1 (as a relation)
-- statement:
--   Algorithm 1 extends a valid $k$-coloring of $S$ to $S \cup \{h\}$. At the head of its while-loop it holds a coloring and a search sequence $T$. One **iteration** does the following:
--
--   1. (Step 5) pick any adding pair $(a, j)$ for $T$ (no choice rule is fixed);
--   2. (Step 6) compute the blocking set $R$;
--   3. (build) if $R \ne \emptyset$, append the layer $(a, j, R)$ and end the iteration;
--   4. (return) if $R = \emptyset$ and $a = h$, add $h$ to $S_j$ and return the coloring;
--   5. (collapse) if $R = \emptyset$ and $a \ne h$, let $i'$ be the layer whose blocking set contains $a$, $j' = c(T^{i'})$, $a' = A(T^{i'})$; recolor $a$ from $j'$ to $j$, cut $T$ to $(T^1, \dots, T^{i'-1})$, and go back to Step 6 with $(a', j')$, **within the same iteration**.
--
--   **Formalization Note** `Step6` is an inductive relation whose derivations are the finite chains of collapses ending in a build (`Outcome.next` with the new coloring and sequence) or a return (`Outcome.done` with the returned coloring); `Iter` adds the choice of Step 5. Because the choice is free, statements about runs quantify over every choice.
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), §3.1, Algorithm 1, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_PolymatroidCover_IsAddingPair
import Definitions.Def_PolymatroidCover_IsBlockingSet
import Definitions.Def_PolymatroidCover_collapseColoring

namespace PolymatroidCover

/-- The outcome of one while-loop iteration of Algorithm 1: either the loop continues from a
new header state (coloring, search sequence), or the algorithm returns a coloring. -/
inductive Outcome (n k : ℕ) where
  /-- the iteration ended with a build step; the loop continues from `(col, T)` -/
  | next (col : Fin k → Finset (Fin n)) (T : List (Layer n k))
  /-- the iteration returned the coloring `col` (line 15) -/
  | done (col : Fin k → Finset (Fin n))

/-- Steps 6–23 of Algorithm 1 (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), printed p.14 = PDF p.16), entered with the coloring `col`,
the search sequence `T` and the pair `(a, j)`:
* `build` (lines 7–11): the blocking set `R` of Step 6 is nonempty; the layer `(a, j, R)` is
  appended and the iteration ends;
* `finish` (lines 13–15): `R = ∅` and `a = h`; `h` is added to `S_j` and the coloring is
  returned;
* `collapse` (lines 16–23): `R = ∅`, `a ≠ h`, `a ∈ B(T^{i'})`; `a` is recolored from
  `j' = c(T^{i'})` to `j`, the sequence is cut to `T^{<i'}`, and Step 6 is re-entered with
  `(a', j') = (A(T^{i'}), c(T^{i'}))` **inside the same iteration** (line 23 goes to Step 6,
  not to line 4).

**Formalization Note** This is a relation (an inductive predicate): each derivation is one
finite chain of collapses ending in a build or a return. `i'` is 0-based (`T[i']` is the
paper's `T^{i'+1}`, `T.take i'` its `T^{<i'+1}`). The blocking set is any `R` satisfying
`IsBlockingSet`; for a polymatroid it is unique (Lemma 2.3). -/
inductive Step6 {n k : ℕ} (f : Finset (Fin n) → ℕ) (h : Fin n) :
    (Fin k → Finset (Fin n)) → List (Layer n k) → Fin n → Fin k → Outcome n k → Prop
  | build (col : Fin k → Finset (Fin n)) (T : List (Layer n k)) (a : Fin n) (j : Fin k)
      (R : Finset (Fin n)) :
      IsBlockingSet f col T a j R → R.Nonempty →
      Step6 f h col T a j (.next col (T ++ [⟨a, j, R⟩]))
  | finish (col : Fin k → Finset (Fin n)) (T : List (Layer n k)) (a : Fin n) (j : Fin k) :
      IsBlockingSet f col T a j ∅ → a = h →
      Step6 f h col T a j (.done (addColoring col h j))
  | collapse (col : Fin k → Finset (Fin n)) (T : List (Layer n k)) (a : Fin n) (j : Fin k)
      (i' : ℕ) (hi' : i' < T.length) (out : Outcome n k) :
      IsBlockingSet f col T a j ∅ → a ≠ h → a ∈ (T[i']'hi').block →
      Step6 f h (collapseColoring col a j (T[i']'hi').color) (T.take i')
        (T[i']'hi').add (T[i']'hi').color out →
      Step6 f h col T a j out

/-- One while-loop iteration of Algorithm 1 (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), printed p.14 = PDF p.16), from the loop header
with coloring `col` and search sequence `T`: Step 5 picks **any** adding pair `(a, j)` (the
algorithm fixes no choice rule), and Steps 6–23 run as `Step6`. -/
def Iter {n k : ℕ} (f : Finset (Fin n) → ℕ) (h : Fin n) (col : Fin k → Finset (Fin n))
    (T : List (Layer n k)) (out : Outcome n k) : Prop :=
  ∃ (a : Fin n) (j : Fin k), IsAddingPair f h T a j ∧ Step6 f h col T a j out

end PolymatroidCover


