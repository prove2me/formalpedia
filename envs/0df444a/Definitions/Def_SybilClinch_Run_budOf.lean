-- Prove2me | Definitions.Def_SybilClinch_Run_budOf
-- name    : SybilClinch_Run_budOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:40:27.41067+00:00
-- url     : https://prove2.me/theorems/757b4059-5dd7-4b1f-94f5-002f224b2af2
-- title:
--   Aggregate effective budget $B_I$
-- statement:
--   For a set $I$ of identities, $B_I=\sum_{i\in I}b_i$ is its aggregate effective remaining budget; for the whole profile it is $B$.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.2, p.9 (PDF p.11); §4.6, (45), p.22 (PDF p.24)

import Mathlib
import Definitions.Def_SybilClinch_Run_bud

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.2, printed p.9 (PDF p.11), and §4.6, (45), printed p.22 (PDF p.24): the aggregate
effective remaining budget `B_I = Σ_{i ∈ I} bᵢ` of a set `I` of identities; for `I = ids` it is
`B`. -/
noncomputable def Run.budOf (M : TargetMech) (P : OneSidedProfile) (R : Run) (I : Finset ℕ)
    (p : ℝ) : ℝ :=
  ∑ i ∈ I, R.bud M P i p

end SybilClinch


