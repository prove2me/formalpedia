-- Prove2me | Definitions.Def_CEPolytopeHard_MLGame_encode
-- name    : CEPolytopeHard_MLGame_encode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:30.060654+00:00
-- url     : https://prove2.me/theorems/b61815fa-c6dd-4744-b73b-a5f3566f1ad3
-- title:
--   Binary encoding of a multilinear polytope game
-- statement:
--   The **encoding** of a multilinear polytope game is a bit string: the length-prefixed list of its players, each player written as its dimension, its length-prefixed list of inequality rows and its length-prefixed list of monomials; every rational $p/q$ is written as a signed numerator and a denominator, and every natural number in binary with a unary length prefix. The **encoding length** $N$ of the game is the length of this string.
--
--   So the length of a number's code is proportional to its bit length, as in Section 2.1 ("All numbers are rational numbers encoded in binary"), and $N$ is "the total encoding length of this game description" (Section 2.3).
--
--   **Formalization Note** The natural-number and rational codes are the published `CorrelatedAuctionComplexity.Main.pack` and `ratCode`. The encoding is injective (checked in the mission's verification file), so an instance string determines its game.
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Section 2.3, p.11 ("We write N for the total encoding length of this game description") and Section 2.1, p.10

import Mathlib
import Definitions.Def_CorrelatedAuctionComplexity_Main_BinaryCodec
import Definitions.Def_CEPolytopeHard_lenList
import Definitions.Def_CEPolytopeHard_MLGame

set_option autoImplicit false

namespace CEPolytopeHard

open CorrelatedAuctionComplexity.Main

/-- code of an inequality row `(a, b)`: the length-prefixed rational coefficients, then `b` -/
def encRow (r : List ℚ × ℚ) : List ℕ := lenList ratCode r.1 ++ ratCode r.2

/-- code of a monomial `(coef, vars)`: `coef`, then the length-prefixed variable pairs -/
def encMono (m : ℚ × List (ℕ × ℕ)) : List ℕ :=
  ratCode m.1 ++ lenList (fun v => [v.1, v.2]) m.2

/-- code of one player: dimension, length-prefixed rows, length-prefixed monomials -/
def encPlayer (P : MLPlayer) : List ℕ :=
  P.dim :: (lenList encRow P.rows ++ lenList encMono P.monos)

/-- The **binary encoding of a multilinear polytope game** (Anagnostides–Daskalakis–Farina–
Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*,
arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, Section 2.3, p.11:
"We write N for the total encoding length of this game description"; Section 2.1, p.10: "All
numbers are rational numbers encoded in binary"). The game is written as the length-prefixed list
of its players; each player as its dimension, its inequality rows and its monomials; each rational
as a signed numerator and a denominator (public `ratCode`); all natural numbers in binary with a
unary length prefix (public `pack`). `N` is the length of this bit string.

**Formalization Note** Every list carries its length, so the code is uniquely decodable; the
encoding length of a number is proportional to its bit length. -/
def MLGame.encode (G : MLGame) : Bits := pack (lenList encPlayer G.players)

end CEPolytopeHard


