-- Prove2me | Definitions.Def_ZeroOneExpansion_compatR
-- name    : ZeroOneExpansion_compatR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:22:06.809222+00:00
-- url     : https://prove2.me/theorems/5b0a6649-4175-4bce-a4c2-4249baf17935
-- title:
--   One-block compatibility relation $\mathcal R\subseteq C\times D$
-- statement:
--   The **one-block compatibility relation** is
--   $$\mathcal R=\{(00,00),(10,10),(01,01),(11,10),(11,01)\}\subseteq C\times D,$$
--   where $10=(1,0)$ and $01=(0,1)$. It records which pairs (point of $C$, point of $D$) can be selected simultaneously as unique maximizers of one linear objective (Lemma 9), and so describes the cross-layer edges of $P_n$ (Corollary 10).
-- source:
--   Yang, 0/1-Polytopes with Exponentially Small Edge Expansion, arXiv:2608.01870 (pdf sha256 53e57bdc2a5505f50b990dfb27d47df0f7d5e2feffc89b808f29d40cff38be53), Lemma 9, p.5, display of R

import Mathlib
import Definitions.Def_ZeroOneExpansion_Pn

set_option autoImplicit false

namespace ZeroOneExpansion

/-- The **one-block compatibility relation**
`R := {(00, 00), (10, 10), (01, 01), (11, 10), (11, 01)} ⊆ C × D` (arXiv:2608.01870, Lemma 9, p.5).
The first component is a point of `C`, the second a point of `D`; `10 = (1, 0)`, `01 = (0, 1)`. -/
def compatR : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ)) :=
  {(![0, 0], ![0, 0]), (![1, 0], ![1, 0]), (![0, 1], ![0, 1]), (![1, 1], ![1, 0]),
    (![1, 1], ![0, 1])}

end ZeroOneExpansion


