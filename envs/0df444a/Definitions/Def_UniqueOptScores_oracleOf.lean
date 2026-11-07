-- Prove2me | Definitions.Def_UniqueOptScores_oracleOf
-- name    : UniqueOptScores_oracleOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:06.076134+00:00
-- url     : https://prove2.me/theorems/83f35f81-b756-4c00-ba0b-63505a1d0eb1
-- title:
--   The language of a point of oracle Cantor space
-- statement:
--   A point $\chi : \{0,1\}^* \to \{0,1\}$ of oracle Cantor space is identified with the oracle $\{w : \chi(w) = 1\}$.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 1.2.3, p.3; Section 8, p.29

import Mathlib

namespace UniqueOptScores

/-- **The language of a point of oracle Cantor space.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §1.2.3, p.3 and §8, p.29 (oracles as points of Cantor space).

`oracleOf χ = {w | χ w = true}`. -/
def oracleOf (χ : List Bool → Bool) : Set (List Bool) :=
  {w | χ w = true}

end UniqueOptScores


