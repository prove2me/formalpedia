-- Prove2me | Definitions.Def_SybilClinch_Run_waterLevel
-- name    : SybilClinch_Run_waterLevel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:41:39.785193+00:00
-- url     : https://prove2.me/theorems/eb2d30e0-03e7-4a0a-8ec7-910b6e20ca6e
-- title:
--   Water level $h=B-pS$
-- statement:
--   The water level is $h:=B-pS$, the aggregate effective budget minus the cost at the clock price of the residual supply. An active identity satisfies the supply invariant exactly when $b_i\le h$, with equality for clinchers.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.2, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_SybilClinch_Run_budOf
import Definitions.Def_SybilClinch_Run_resid

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.2, printed p.10 (PDF p.12): the water level `h := B − pS`. -/
noncomputable def Run.waterLevel (M : TargetMech) (P : OneSidedProfile) (R : Run) (p : ℝ) : ℝ :=
  R.budOf M P P.ids p - p * R.resid M P p

end SybilClinch


