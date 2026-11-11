-- Prove2me | Definitions.Def_SybilClinch_Run_beta
-- name    : SybilClinch_Run_beta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:41:51.784593+00:00
-- url     : https://prove2.me/theorems/9f5af3ba-c320-454f-a5c1-fe20e8ced687
-- title:
--   $\beta=Y+B$
-- statement:
--   $\beta:=Y+B$ is the aggregate payment plus the aggregate effective remaining budget of all identities; it equals the sum of the initial budgets minus the cancelled budgets.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.6, Lemma 4.17, (50), p.23 (PDF p.25)

import Mathlib
import Definitions.Def_SybilClinch_Run_payOf
import Definitions.Def_SybilClinch_Run_budOf

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.6, Lemma 4.17, (50), printed p.23 (PDF p.25): `β := Y + B`, the aggregate payment plus
the aggregate effective remaining budget of all identities. -/
noncomputable def Run.beta (M : TargetMech) (P : OneSidedProfile) (R : Run) (p : ℝ) : ℝ :=
  R.payOf M P.ids p + R.budOf M P P.ids p

end SybilClinch


