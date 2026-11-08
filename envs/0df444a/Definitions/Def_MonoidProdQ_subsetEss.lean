-- Prove2me | Definitions.Def_MonoidProdQ_subsetEss
-- name    : MonoidProdQ_subsetEss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:50:41.662063+00:00
-- url     : https://prove2.me/theorems/9f858e1d-b729-49bf-840e-e9cc8b7ab1cb
-- title:
--   Essential positions of the subset-product summary
-- statement:
--   For a commutative monoid $M$, a word $x\in G^s$ and $T\subseteq[s]$, the essential positions of the subset-product summary are
--
--   $$\mathrm{Ess}_x(T)=\{\,i\in T : p_x(T)\ne p_x(T\setminus\{i\})\,\}:$$
--
--   the revealed letters whose deletion changes the product of the revealed letters.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §5.1, Eq. (16), p.33

import Definitions.Def_MonoidProdQ_subsetProd

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §5.1, Eq. (16), p.33: the essential positions of the subset-product summary,
`Essₓ(T) = {i ∈ T : pₓ(T) ≠ pₓ(T \ {i})}`. -/
def subsetEss {M : Type*} [CommMonoid M] [DecidableEq M] {G : Finset M} {s : ℕ}
    (x : Fin s → G) (T : Finset (Fin s)) : Finset (Fin s) :=
  T.filter fun i => subsetProd x T ≠ subsetProd x (T.erase i)

end MonoidProdQ


