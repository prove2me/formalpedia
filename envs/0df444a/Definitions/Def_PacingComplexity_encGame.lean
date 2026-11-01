-- Prove2me | Definitions.Def_PacingComplexity_encGame
-- name    : PacingComplexity_encGame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:15.693717+00:00
-- url     : https://prove2.me/theorems/f9104921-1324-43ca-a832-53457145f0bd
-- title:
--   Binary encoding of a rational SPP game
-- statement:
--   A rational SPP game $G=(n,m,(v_{ij}),(B_i))$ is encoded as the code of its $n\times m$ value matrix followed by the code of its budget vector ($n$ in binary, then the $n$ rational budgets).
--
--   This is the input format of the search problem APPROX-PACING$_c$.
-- source:
--   Chen, Kroer, Kumar, The Complexity of Pacing for Second-Price Auctions, arXiv:2103.13969v2, §2, p.6; p.3 (rational values and budgets); p.19 (input size |G|)

import Mathlib
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_PacingComplexity_encRatRect

namespace PacingComplexity

/-- **Binary encoding of a rational SPP game** `G = (n, m, (vij), (Bi))` (Chen, Kroer, Kumar,
*The Complexity of Pacing for Second-Price Auctions*, arXiv:2103.13969v2, §2, p.6): the
rectangular code of the values (`encRatRect n m v`) followed by the vector code of the budgets
(`CardinalMatching.encRatVec n B`, which repeats `n` in binary, then the `n` budgets).

**Formalization Note** Rational data in binary, as in "when values and budgets of buyers are
rational" (p.3) and the bit size `|G|` of p.19. -/
def encGame (n m : ℕ) (v : Fin n → Fin m → ℚ) (B : Fin n → ℚ) : List Bool :=
  encRatRect n m v ++ CardinalMatching.encRatVec n B

end PacingComplexity


