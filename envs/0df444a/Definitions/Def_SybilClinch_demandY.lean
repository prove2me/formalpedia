-- Prove2me | Definitions.Def_SybilClinch_demandY
-- name    : SybilClinch_demandY
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:41:27.753083+00:00
-- url     : https://prove2.me/theorems/7fde785d-d17a-43bb-a188-d154536ed28d
-- title:
--   Sell-$Y$ side at the spot price $D_Y=\sum_{E_Y}q_i/p_0$
-- statement:
--   Measured at the spot price in units of $X$, the sell-$Y$ side is $D_Y:=\sum_{i\in E_Y}q_i/p_0$.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.1, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_SybilClinch_eligY

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.1, printed p.25 (PDF p.27): the sell-`Y` side measured at the spot price in units of
`X`, `D_Y := Σ_{i ∈ E_Y} qᵢ/p₀`. -/
noncomputable def demandY (A : AdmissibleAMM) (ids : Finset ℕ) (rep : ℕ → Report) : ℝ :=
  ∑ i ∈ eligY A ids rep, (rep i).bud / A.p0

end SybilClinch


