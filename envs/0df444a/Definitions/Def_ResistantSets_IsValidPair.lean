-- Prove2me | Definitions.Def_ResistantSets_IsValidPair
-- name    : ResistantSets_IsValidPair
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:26:09.941993+00:00
-- url     : https://prove2.me/theorems/adbb6003-8aec-40f8-815c-e87f0dd935ac
-- title:
--   Valid pair $[x,y]$ ("$x$ sees $y$")
-- statement:
--   Let $S\subseteq\{0,1\}^n$. A **valid pair** is a pair $[x,y]$ where $x$ is infeasible, $y$ is feasible, and $y\triangle x$ is a minimal point of $S\triangle x$. If $[x,y]$ is a valid pair, $x$ **sees** $y$.
--
--   Valid pairs are the objects moved by the Sight Propagation Lemma 4.8.
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, p.17, §4.2 (valid pair)

import Mathlib
import Definitions.Def_ResistantSets_twist
import Definitions.Def_ResistantSets_IsMinimalPoint

namespace ResistantSets

/-- **Valid pair** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), §4.2, p.17): "A valid pair is a pair [x, y] where x is infeasible, y is
feasible, and y△x is a minimal feasible point of S△x. If [x, y] is a valid pair, we will say that
x sees y." -/
def IsValidPair {n : ℕ} (S : Finset (Fin n → Bool)) (x y : Fin n → Bool) : Prop :=
  x ∉ S ∧ y ∈ S ∧ IsMinimalPoint (twist S x) (vxor y x)

end ResistantSets


