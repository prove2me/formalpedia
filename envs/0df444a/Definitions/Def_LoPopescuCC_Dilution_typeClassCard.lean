-- Prove2me | Definitions.Def_LoPopescuCC_Dilution_typeClassCard
-- name    : LoPopescuCC_Dilution_typeClassCard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:41:56.089835+00:00
-- url     : https://prove2.me/theorems/98477624-b444-4c2b-b0c4-456556dcdf0c
-- title:
--   Size of a type class
-- statement:
--   The type class of a string $x$ is the set of strings with the same count vector as $x$. This is its size. For two letters and a string with $m$ occurrences of one letter it is the binomial coefficient $\binom{N}{m}$ of the paper. It is at least $1$.
-- source:
--   Lo, Popescu, The classical communication cost of entanglement manipulation, arXiv:quant-ph/9902045v2, Proof of the Theorem, p. 5

import Mathlib
import Definitions.Def_LoPopescuCC_Dilution_typeCount

namespace LoPopescuCC.Dilution

/-- **Size of the type class of a string** (Lo, Popescu, arXiv:quant-ph/9902045v2, Proof of the
Theorem, p. 5): the number of strings `y` with the same count vector as `x`. For `k = 2` and `x`
with `m` ones this is the paper's binomial coefficient `C(N, m)`. It is at least `1`, since `x`
itself is counted. -/
def typeClassCard {k N : ℕ} (x : Fin N → Fin k) : ℕ :=
  (Finset.univ.filter fun y : Fin N → Fin k => typeCount y = typeCount x).card

end LoPopescuCC.Dilution


