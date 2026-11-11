-- Prove2me | Definitions.Def_SybilClinch_Run_stopTest
-- name    : SybilClinch_Run_stopTest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:41:50.203141+00:00
-- url     : https://prove2.me/theorems/6fcaeec9-64a4-4c2e-8582-209b72e1e97a
-- title:
--   Stopping test $\sum_{\mathrm{Active}} b_i/p\le S$
-- statement:
--   At clock price $p$, after incorporating a possible lump and before cancelling any budget or making any restoration purchase, the stopping test is
--   $$\sum_{i\in\mathrm{Active}}\frac{b_i}{p}\le S.\qquad(20)$$
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.4, (20), p.11 (PDF p.13)

import Mathlib
import Definitions.Def_SybilClinch_Run_preActive
import Definitions.Def_SybilClinch_Run_preResid

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.4, (20), printed p.11 (PDF p.13): the stopping test at clock price `p`, evaluated after
incorporating a possible lump and before cancelling any budget:
`Σ_{i ∈ Active} bᵢ/p ≤ S`. -/
def Run.stopTest (M : TargetMech) (P : OneSidedProfile) (R : Run) (p : ℝ) : Prop :=
  (∑ i ∈ R.preActive M P p, R.budPre M P i p) / p ≤ R.preResid M P p

end SybilClinch


