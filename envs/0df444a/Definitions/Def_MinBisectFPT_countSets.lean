-- Prove2me | Definitions.Def_MinBisectFPT_countSets
-- name    : MinBisectFPT_countSets
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:27.199208+00:00
-- url     : https://prove2.me/theorems/4f87f958-e215-4e6d-a190-fd6ac7ce2175
-- title:
--   The numbers $C_G(\ell,j)$
-- statement:
--   For a graph $G$ and integers $\ell,j\ge 0$,
--   $$C_G(\ell,j)=\bigl|\{X\subseteq V(G): |X|=\ell\text{ and }|\delta(X)|=j\}\bigr|.$$
--   These numbers are the output of the mission's main theorem. A bisection of width $j$ corresponds to a set of size $\lfloor n/2\rfloor$ with cut $j$.
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), Theorem 1.1, p.2

import Mathlib
import Definitions.Def_MinBisectFPT_cutSize

open scoped Classical

namespace MinBisectFPT

/-- **The numbers `C_G(ℓ, j)`.** Anand, Kipouridis, Węgrzycki, *Counting over Unbreakable
Decompositions*, STOC 2027 submission (manuscript sha256 8db80a52…), Theorem 1.1, p.2:
`C_G(ℓ, j) = |{X ⊆ V(G) : |X| = ℓ and |δ(X)| = j}|`. -/
noncomputable def countSets {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (l j : ℕ) :
    ℕ :=
  (Finset.univ.filter fun X : Finset V => X.card = l ∧ cutSize G X = j).card

end MinBisectFPT


