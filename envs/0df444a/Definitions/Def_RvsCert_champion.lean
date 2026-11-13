-- Prove2me | Definitions.Def_RvsCert_champion
-- name    : RvsCert_champion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:46:17.072603+00:00
-- url     : https://prove2.me/theorems/55ed5de0-3fea-43a6-b928-914832565211
-- title:
--   The champion function $f$
-- statement:
--   The total Boolean function of the paper: $f(X,Y)=1$ if and only if some athlete is the champion of $(X,Y)$. It is defined on every bit string, whether or not the lists and cards are well formatted.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Section 2, Formal definition, p.2

import Mathlib
import Definitions.Def_RvsCert_IsChampion

namespace RvsCert

/-- **The function `f`** (Formal definition, Section 2, p.2 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1: "Set
f(X, Y) = 1 if and only if there exists an athlete (c, b) ∈ C × B who satisfies these
conditions"). A total Boolean function on the bit strings `Idx n → Bool`. -/
def champion (n : ℕ) (x : Idx n → Bool) : Bool :=
  decide (∃ a : Fin (2 * n) × Fin n, IsChampion n x a)

end RvsCert


