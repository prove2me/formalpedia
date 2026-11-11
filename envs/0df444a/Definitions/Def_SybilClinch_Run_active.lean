-- Prove2me | Definitions.Def_SybilClinch_Run_active
-- name    : SybilClinch_Run_active
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:40:20.009928+00:00
-- url     : https://prove2.me/theorems/f23b2a19-98f5-42bc-8034-f671b88e0fc3
-- title:
--   Active identities
-- statement:
--   At clock price $p$ (after the events at $p$), the active identities are $\mathrm{Active}=\{i:v_i>p,\ b_i>0\}$ (12).
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.2, (12), p.9 (PDF p.11)

import Mathlib
import Definitions.Def_SybilClinch_Run_bud

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.2, (12), printed p.9 (PDF p.11): the active identities `Active = {i : vᵢ > p, bᵢ > 0}`
at clock price `p` (after the events at `p`). -/
noncomputable def Run.active (M : TargetMech) (P : OneSidedProfile) (R : Run) (p : ℝ) :
    Finset ℕ :=
  P.ids.filter (fun i => (p : WithTop ℝ) < P.v i ∧ 0 < R.bud M P i p)

end SybilClinch


