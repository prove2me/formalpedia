-- Prove2me | Definitions.Def_SybilClinch_flowY
-- name    : SybilClinch_flowY
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:38:55.650526+00:00
-- url     : https://prove2.me/theorems/dd6a28ac-162b-4973-ae30-2c3d0f36cec3
-- title:
--   Net $Y$ paid by a set of identities
-- statement:
--   For a set $I$ of identities,
--   $$\mathrm{flow}_Y(I):=\sum_{i\in I,\ \text{sell-}Y}S_{Y,i}-\sum_{i\in I,\ \text{sell-}X}R_{Y,i}.$$
--   For the whole profile this is the pool's net receipt $Y_{\rm pool}$ of (3). For the identities of a physical trader $k$ it is $-\Delta_{Y,k}=S_Y(k)-R_Y(k)$, its net sale of $Y$, (4).
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.1, (3), p.6 (PDF p.8); §2.2, (4), p.7 (PDF p.9)

import Mathlib
import Definitions.Def_SybilClinch_Report
import Definitions.Def_SybilClinch_Fill

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.1, (3), printed p.6 (PDF p.8), and §2.2, (4), printed p.7 (PDF p.9): the net amount of
`Y` paid by a set of identities,
`Σ_{i ∈ I, sell-Y} S_{Y,i} − Σ_{i ∈ I, sell-X} R_{Y,i}`.

For the whole reported profile this is the pool's net receipt `Y_pool` of (3); for the identities of
a physical trader `k` it is `−Δ_{Y,k} = S_Y(k) − R_Y(k)` of (4). -/
def flowY (I : Finset ℕ) (rep : ℕ → Report) (f : ℕ → Fill) : ℝ :=
  (∑ i ∈ I.filter (fun i => (rep i).dir = Dir.sellY), (f i).sold) -
    ∑ i ∈ I.filter (fun i => (rep i).dir = Dir.sellX), (f i).recv

end SybilClinch


