-- Prove2me | Definitions.Def_LoPopescuCC_Dilution_typeCount
-- name    : LoPopescuCC_Dilution_typeCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:41:12.920098+00:00
-- url     : https://prove2.me/theorems/e5b20a59-3062-4c61-ba5e-f0fd9af60c89
-- title:
--   Count vector of a string
-- statement:
--   For a string $x$ of length $N$ over the alphabet $\{0,\dots,k-1\}$, the count vector records, for each letter $i$, the number of positions $j$ with $x_j=i$. For $k=2$ it carries the same information as the paper's index $k$ in the coefficient $a^kb^{N-k}$.
-- source:
--   Lo, Popescu, The classical communication cost of entanglement manipulation, arXiv:quant-ph/9902045v2, Proof of the Theorem, p. 5

import Mathlib

namespace LoPopescuCC.Dilution

/-- **Count vector (type) of a string** (Lo, Popescu, arXiv:quant-ph/9902045v2, Proof of the
Theorem, p. 5): `typeCount x i` is the number of positions `j` with `x_j = i`. For `k = 2` this is
the paper's index `k`, the number of factors `a` in the coefficient `a^k b^{N−k}`. -/
def typeCount {k N : ℕ} (x : Fin N → Fin k) (i : Fin k) : ℕ :=
  (Finset.univ.filter fun j => x j = i).card

end LoPopescuCC.Dilution


