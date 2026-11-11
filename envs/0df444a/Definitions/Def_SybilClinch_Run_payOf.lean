-- Prove2me | Definitions.Def_SybilClinch_Run_payOf
-- name    : SybilClinch_Run_payOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:39:11.868732+00:00
-- url     : https://prove2.me/theorems/92e3aebb-40bd-49be-b891-7965ecc12443
-- title:
--   Cumulative payment $Y_I(p)$ of a set of identities
-- statement:
--   For a set $I$ of identities, $Y_I(p)=\sum_{i\in I}y_i(p)$ is its cumulative payment through clock price $p$. For $I$ the whole profile it is the aggregate payment $Y$ of (8).
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.1, (8), p.9 (PDF p.11); §4.6, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_SybilClinch_Run_pay

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.1, (8), printed p.9 (PDF p.11), and §4.6, printed p.21 (PDF p.23): the cumulative
payment `Y_I(p) = Σ_{i ∈ I} yᵢ(p)` of a set `I` of identities through clock price `p`. For
`I = ids` it is the aggregate payment `Y`. -/
noncomputable def Run.payOf (M : TargetMech) (R : Run) (I : Finset ℕ) (p : ℝ) : ℝ :=
  ∑ i ∈ I, R.pay M i p

end SybilClinch


