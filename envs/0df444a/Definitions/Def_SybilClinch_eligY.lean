-- Prove2me | Definitions.Def_SybilClinch_eligY
-- name    : SybilClinch_eligY
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:40:26.655201+00:00
-- url     : https://prove2.me/theorems/9ceb31d5-6be4-4a27-ad42-011e40461df8
-- title:
--   Eligible sell-$Y$ identities $E_Y$
-- statement:
--   $E_Y$ is the set of reported sell-$Y$ identities with value $v_i\ge p_0$.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.1, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_SybilClinch_IsEligible

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.1, printed p.25 (PDF p.27): the eligible sell-`Y` identities `E_Y ⊆ I_Y` (`vᵢ ≥ p₀`). -/
noncomputable def eligY (A : AdmissibleAMM) (ids : Finset ℕ) (rep : ℕ → Report) : Finset ℕ :=
  ids.filter (fun i => (rep i).dir = Dir.sellY ∧ A.p0 ≤ (rep i).val)

end SybilClinch


