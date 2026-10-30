-- Prove2me | Definitions.Def_JailletLu_Astar
-- name    : JailletLu_Astar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:23:00.943796+00:00
-- url     : https://prove2.me/theorems/99f306fa-f89e-4d40-905d-220c8b07fe9c
-- title:
--   The set $A^*_a=A^*\setminus\{a\}$
-- statement:
--   With $A^*=A\cup\{a_d\}$ the advertisers together with the dummy, $A^*_a=A^*\setminus\{a\}$ for $a\in A$. It always contains the dummy $a_d$, so it is nonempty.
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, p. 14

import Mathlib

namespace JailletLu

/-- **The set `A*_a = (A ∪ {a_d}) \ {a}`.**
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, p. 14: "Let A_a = A\{a}, A* = A∪{a_d}, and A*_a = A*\{a}."

With `A* = Option A` (`none` = `a_d`), `Astar a` is the finite set of all `b : Option A` other
than `some a`. It always contains the dummy `none`. -/
def Astar {A : Type*} [Fintype A] [DecidableEq A] (a : A) : Finset (Option A) :=
  Finset.univ.erase (some a)

end JailletLu


