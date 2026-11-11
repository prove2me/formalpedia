-- Prove2me | Definitions.Def_SybilClinch_IsEligible
-- name    : SybilClinch_IsEligible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:39:10.366629+00:00
-- url     : https://prove2.me/theorems/a139753d-6578-4c2e-9bd6-1d0c09bbe3e3
-- title:
--   Eligibility of an order
-- statement:
--   A sell-$Y$ order is **eligible** if its value satisfies $v_i\ge p_0$, and a sell-$X$ order is eligible if $u_i\le p_0$, where $p_0$ is the spot price.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.1, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_SybilClinch_AdmissibleAMM_p0
import Definitions.Def_SybilClinch_Report

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.1, printed p.5 (PDF p.7): a sell-`Y` order is eligible if `vᵢ ≥ p₀`, and a sell-`X`
order is eligible if `uᵢ ≤ p₀`. -/
def IsEligible (A : AdmissibleAMM) (r : Report) : Prop :=
  (r.dir = Dir.sellY ∧ A.p0 ≤ r.val) ∨ (r.dir = Dir.sellX ∧ r.val ≤ A.p0)

end SybilClinch


