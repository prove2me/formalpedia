-- Prove2me | Definitions.Def_HolevoCQ_sqrtMeas
-- name    : HolevoCQ_sqrtMeas
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:16:16.829979+00:00
-- url     : https://prove2.me/theorems/73c19132-dbfc-4619-beb5-7d087f894d76
-- title:
--   Square-root decision operators (eq. 11)
-- statement:
--   Given positive operators $B_1,\dots,B_N$, put
--
--   $$
--   X_u=\Big(\sum_{u'=1}^NB_{u'}\Big)^{-1/2}B_u\Big(\sum_{u'=1}^NB_{u'}\Big)^{-1/2},
--   $$
--
--   with the generalized inverse square root. Holevo's suboptimal decision rule (11) is the case $B_u=PP_uP$, with $P$ the typical projector (6) and $P_u$ the typical projector (8) of the $u$-th code word.
--
--   **Formalization Note** Code positions are `Fin N`.
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, eq. (11), p.4

import Mathlib
import Definitions.Def_HolevoCQ_genInvSqrt

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, eq. (11), p.4: the decision operators
`X_u = (Σ_{u'} B_{u'})^{−1/2} B_u (Σ_{u'} B_{u'})^{−1/2}` built from positive operators `B_u`;
the paper's decision rule is `B_u = P P_u P`, with `P` from (6) and `P_u` from (8).

**Formalization Note.** Code positions are `k : Fin N`; `^{−1/2}` is the generalized inverse
`genInvSqrt`. -/
noncomputable def sqrtMeas {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (B : Fin N → Matrix ι ι ℂ) (k : Fin N) : Matrix ι ι ℂ :=
  genInvSqrt (∑ k', B k') * B k * genInvSqrt (∑ k', B k')

end HolevoCQ


