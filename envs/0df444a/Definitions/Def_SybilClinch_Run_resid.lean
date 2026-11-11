-- Prove2me | Definitions.Def_SybilClinch_Run_resid
-- name    : SybilClinch_Run_resid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:40:19.689245+00:00
-- url     : https://prove2.me/theorems/cebc630e-4385-4088-93fb-16ee065d65d3
-- title:
--   Residual supply $S=T(p,X,Y)-X$
-- statement:
--   At clock price $p$ the residual supply offered to the auction is $S=T(p,X,Y)-X$, the target being re-evaluated at the current aggregate state (16).
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.2, p.9 (PDF p.11); §4.1, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_SybilClinch_Run_alloc
import Definitions.Def_SybilClinch_Run_payOf
import Definitions.Def_SybilClinch_OneSidedProfile

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.2, printed p.9 (PDF p.11), and §4.1, printed p.13 (PDF p.15): the residual supply
`S = T(p, X, Y) − X` at clock price `p`, the target being re-evaluated at the current state (16). -/
noncomputable def Run.resid (M : TargetMech) (P : OneSidedProfile) (R : Run) (p : ℝ) : ℝ :=
  M.T p (R.alloc P.ids p) (R.payOf M P.ids p) - R.alloc P.ids p

end SybilClinch


