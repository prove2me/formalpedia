-- Prove2me | Definitions.Def_SybilClinch_eligX
-- name    : SybilClinch_eligX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:40:43.426994+00:00
-- url     : https://prove2.me/theorems/fb73242b-f93c-4d1b-88ca-bc9b05159179
-- title:
--   Eligible sell-$X$ identities $E_X$
-- statement:
--   $E_X$ is the set of reported sell-$X$ identities with value $u_i\le p_0$.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.1, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_SybilClinch_IsEligible

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.1, printed p.25 (PDF p.27): the eligible sell-`X` identities `E_X ⊆ I_X` (`uᵢ ≤ p₀`). -/
noncomputable def eligX (A : AdmissibleAMM) (ids : Finset ℕ) (rep : ℕ → Report) : Finset ℕ :=
  ids.filter (fun i => (rep i).dir = Dir.sellX ∧ (rep i).val ≤ A.p0)

end SybilClinch


