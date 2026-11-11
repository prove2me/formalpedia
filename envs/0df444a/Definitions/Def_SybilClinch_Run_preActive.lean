-- Prove2me | Definitions.Def_SybilClinch_Run_preActive
-- name    : SybilClinch_Run_preActive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:40:42.938348+00:00
-- url     : https://prove2.me/theorems/8c01909c-19f6-47c1-9b7d-59586f1d0141
-- title:
--   Active identities at an event price, before its operations
-- statement:
--   At clock price $p$, before any fixed-price operation, the active identities are those with $v_i>p$ and positive pre-event budget.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.4, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_SybilClinch_Run_budPre

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.4, printed p.11 (PDF p.13): the active identities at an event price `p` before any
fixed-price operation, `{i : vᵢ > p, bᵢ > 0}` on the pre-event budgets. -/
noncomputable def Run.preActive (M : TargetMech) (P : OneSidedProfile) (R : Run) (p : ℝ) :
    Finset ℕ :=
  P.ids.filter (fun i => (p : WithTop ℝ) < P.v i ∧ 0 < R.budPre M P i p)

end SybilClinch


