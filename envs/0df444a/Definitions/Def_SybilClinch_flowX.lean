-- Prove2me | Definitions.Def_SybilClinch_flowX
-- name    : SybilClinch_flowX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:38:47.784253+00:00
-- url     : https://prove2.me/theorems/04b69266-9a13-4f5a-86f7-b09078602cf6
-- title:
--   Net $X$ received by a set of identities
-- statement:
--   For a set $I$ of identities with reports and outcomes,
--   $$\mathrm{flow}_X(I):=\sum_{i\in I,\ \text{sell-}Y}R_{X,i}-\sum_{i\in I,\ \text{sell-}X}S_{X,i}.$$
--   For the whole profile this is the pool's net release $X_{\rm pool}$ of (3). For the identities $\mathcal I_Y(k)\cup\mathcal I_X(k)$ of a physical trader $k$ it is the net change $\Delta_{X,k}=R_X(k)-S_X(k)$ of its $X$ holding, (4).
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.1, (3), p.6 (PDF p.8); §2.2, (4), p.7 (PDF p.9)

import Mathlib
import Definitions.Def_SybilClinch_Report
import Definitions.Def_SybilClinch_Fill

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.1, (3), printed p.6 (PDF p.8), and §2.2, (4), printed p.7 (PDF p.9): the net amount of
`X` received by a set of identities,
`Σ_{i ∈ I, sell-Y} R_{X,i} − Σ_{i ∈ I, sell-X} S_{X,i}`.

For the whole reported profile this is the pool's net release `X_pool` of (3); for the identity
set `I_Y(k) ∪ I_X(k)` of a physical trader `k` it is `Δ_{X,k} = R_X(k) − S_X(k)` of (4). -/
def flowX (I : Finset ℕ) (rep : ℕ → Report) (f : ℕ → Fill) : ℝ :=
  (∑ i ∈ I.filter (fun i => (rep i).dir = Dir.sellY), (f i).recv) -
    ∑ i ∈ I.filter (fun i => (rep i).dir = Dir.sellX), (f i).sold

end SybilClinch


