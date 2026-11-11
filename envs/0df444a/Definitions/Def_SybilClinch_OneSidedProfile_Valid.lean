-- Prove2me | Definitions.Def_SybilClinch_OneSidedProfile_Valid
-- name    : SybilClinch_OneSidedProfile_Valid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:37:49.337795+00:00
-- url     : https://prove2.me/theorems/f9434b97-ef26-4e3e-b657-e068310d6525
-- title:
--   Valid one-sided profile
-- statement:
--   Every identity of the profile reports a nonnegative value (possibly $+\infty$) and a nonnegative budget.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.1, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_SybilClinch_OneSidedProfile

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.1, printed p.8 (PDF p.10): every identity reports `(vᵢ, qᵢ) ∈ ℝ²_{≥0}` (value possibly
`+∞` in the reverse auction of §5.2). -/
def OneSidedProfile.Valid (P : OneSidedProfile) : Prop :=
  ∀ i ∈ P.ids, 0 ≤ P.v i ∧ 0 ≤ P.q i

end SybilClinch


