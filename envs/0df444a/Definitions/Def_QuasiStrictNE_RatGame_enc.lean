-- Prove2me | Definitions.Def_QuasiStrictNE_RatGame_enc
-- name    : QuasiStrictNE_RatGame_enc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:56.34307+00:00
-- url     : https://prove2.me/theorems/1ea7644d-c3d1-4d51-80b1-142861b36f54
-- title:
--   Binary code of a rational bimatrix game
-- statement:
--   The **code** of a rational bimatrix game $(A,B)$ is the code of $A$ followed by the code of $B$, each written as: $m$ and $n$ in self-delimiting binary, then the $mn$ entries in row-major order as reduced fractions. Its length is the input size $|I|$.
--
--   **Formalization Note** The paper fixes no encoding; this one is built from the public `PacingComplexity.encRatRect`, and every code is self-delimiting.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Definition 1, p.4 (the input I = (A, B))

import Mathlib
import Definitions.Def_PacingComplexity_encRatRect
import Definitions.Def_QuasiStrictNE_RatGame

namespace QuasiStrictNE

/-- **Binary code of a rational bimatrix game** (Hansen & Nie, *On Existence and Computational
Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, Definition 1, p.4; the input `I = (A, B)`
of the computational problem, whose size `|I|` is the length of this code).

The code is the code of `A` followed by the code of `B`, each written by the public
`PacingComplexity.encRatRect` (`m`, `n` in self-delimiting binary, then the entries in row-major
order as reduced fractions).

**Formalization Note** The paper fixes no encoding. Every code is self-delimiting, so a string is the
code of at most one game. -/
def RatGame.enc (G : RatGame) : List Bool :=
  PacingComplexity.encRatRect G.m G.n G.A ++ PacingComplexity.encRatRect G.m G.n G.B

end QuasiStrictNE


