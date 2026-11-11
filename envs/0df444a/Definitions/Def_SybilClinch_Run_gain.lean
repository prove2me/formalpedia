-- Prove2me | Definitions.Def_SybilClinch_Run_gain
-- name    : SybilClinch_Run_gain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:40:10.123461+00:00
-- url     : https://prove2.me/theorems/df69b959-c295-4ae0-850b-9e58d040695e
-- title:
--   Mark-to-market gain $\Gamma_I(p)=pX_I(p)-Y_I(p)$
-- statement:
--   For a set $I$ of identities, the mark-to-market gain is
--   $$\Gamma_I(p):=p\,X_I(p)-Y_I(p).\qquad(44)$$
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.6, (44), p.21 (PDF p.23)

import Mathlib
import Definitions.Def_SybilClinch_Run_alloc
import Definitions.Def_SybilClinch_Run_payOf

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.6, (44), printed p.21 (PDF p.23): the mark-to-market gain of a set `I` of identities,
`Γ_I(p) := p·X_I(p) − Y_I(p)`. -/
noncomputable def Run.gain (M : TargetMech) (R : Run) (I : Finset ℕ) (p : ℝ) : ℝ :=
  p * R.alloc I p - R.payOf M I p

end SybilClinch


