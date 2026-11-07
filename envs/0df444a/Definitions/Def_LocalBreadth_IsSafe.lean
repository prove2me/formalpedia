-- Prove2me | Definitions.Def_LocalBreadth_IsSafe
-- name    : LocalBreadth_IsSafe
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:54:16.358796+00:00
-- url     : https://prove2.me/theorems/75636f3e-2154-49f1-808e-383bdee872a6
-- title:
--   Safe histories and protected sets
-- statement:
--   Let $H$ be a history starting at $A$. It is **$(A,n,q)$-unsafe** if there is an admissible obstruction tree rooted at $\mathrm{end}(H)$ such that every root-to-leaf path, when appended to $H$ with the common language written once, produces a history $H'$ with $c_n(H')\le q$. Otherwise it is **$(A,n,q)$-safe**.
--
--   A **protected set** with respect to $H$ is a finite $\mathrm{Prot}(H)\subseteq\mathrm{end}(H)$ such that every $L\in\mathcal X$ with $\mathrm{Prot}(H)\subseteq L\subsetneq\mathrm{end}(H)$ makes $H^\frown L$ safe.
--
--   Protected sets are the finite certificates the generator's static forest is built from.
--
--   **Formalization Note** A chain is a list; $A$ is its first language, read by $c_n$, so it is not a separate argument. Appending is `c ++ p.tail`.
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), Definition 5.2, p.24; Definition 5.11, p.30

import Mathlib
import Definitions.Def_LocalBreadth_cScore
import Definitions.Def_LocalBreadth_ObsTree

namespace LocalBreadth

/-- `(A, n, q)`-**unsafe**. Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…),
Definition 5.2, p.24: there is an admissible obstruction tree rooted at `end(H)` such that every
root-to-leaf path, when appended to `H`, produces `H′` with `c_n(H′) ≤ q`.

**Formalization Note.** A chain is a list; `A` is its first language, which `c_n` reads, so `A` is not
a separate argument. Appending writes the common language once: `c ++ p.tail`. -/
def IsUnsafe (X : Set (Set ℤ)) (n : ℕ) (q : ℝ) (c : List (Set ℤ)) : Prop :=
  ∃ T : ObsTree, T.Admissible X ∧ T.label = c.getLastD ∅ ∧
    ∀ p ∈ T.paths, cScore n (c ++ p.tail) ≤ q

/-- `(A, n, q)`-**safe**, Definition 5.2, p.24. -/
def IsSafe (X : Set (Set ℤ)) (n : ℕ) (q : ℝ) (c : List (Set ℤ)) : Prop := ¬ IsUnsafe X n q c

/-- A **protected set** with respect to a chain, Definition 5.11, p.30 (Corollary 5.10, item 3): a
finite `Prot(H) ⊆ end(H)` such that every `L ∈ X` with `Prot(H) ⊆ L ⊊ end(H)` makes `H⌢L` safe. -/
def IsProtectedSet (X : Set (Set ℤ)) (n : ℕ) (q : ℝ) (c : List (Set ℤ)) (F : Finset ℤ) : Prop :=
  (F : Set ℤ) ⊆ c.getLastD ∅ ∧
    ∀ L ∈ X, L ⊂ c.getLastD ∅ → (F : Set ℤ) ⊆ L → IsSafe X n q (c ++ [L])

end LocalBreadth


