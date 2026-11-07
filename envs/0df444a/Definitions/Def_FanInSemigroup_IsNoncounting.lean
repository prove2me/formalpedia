-- Prove2me | Definitions.Def_FanInSemigroup_IsNoncounting
-- name    : FanInSemigroup_IsNoncounting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:10.146861+00:00
-- url     : https://prove2.me/theorems/9fb5470f-835b-43e8-9ff9-61a3602e6fd1
-- title:
--   Noncounting language
-- statement:
--   A language $L$ is **noncounting** if there is an $n$ such that for all words $x,y,z$, the empty word included, and all $m\ge n$,
--
--   $$
--   xy^{m}z\in L\iff xy^{m+1}z\in L.
--   $$
--
--   Past a threshold the language cannot distinguish how many times a factor repeats. This is the combinatorial condition linking groupfree semigroups to rs machines.
--
--   **Formalization Note** The page defines this for regular sets. Regularity is not part of this predicate; it is a separate statement wherever it is used.
-- source:
--   Chandra, Fortune, Lipton, Unbounded Fan-in Circuits and Associative Functions, STOC 1983, doi:10.1145/800061.808732, §2, p.55

import Mathlib

set_option autoImplicit false

namespace FanInSemigroup

/-- Noncounting languages. Chandra, Fortune, Lipton, STOC 1983, §2, p.55: "A regular set L is
noncounting if there is an n so that for all x, y, and z and all m≥n, xy^m z∈L iff xy^{m+1} z∈L".
The words `x`, `y`, `z` range over all words, the empty word included.

**Formalization Note.** Regularity is not part of this predicate: the page's regular sets are
carried by `Language.IsRegular` where the statements need it. Taking `n = 0` is harmless: `y^0` is
the empty word, and a witness `0` is in particular a witness `1`. -/
def IsNoncounting {α : Type*} (L : Language α) : Prop :=
  ∃ n : ℕ, ∀ (x y z : List α) (m : ℕ), n ≤ m →
    (x ++ (List.replicate m y).flatten ++ z ∈ L ↔
      x ++ (List.replicate (m + 1) y).flatten ++ z ∈ L)

end FanInSemigroup


