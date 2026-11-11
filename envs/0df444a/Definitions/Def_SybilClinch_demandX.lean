-- Prove2me | Definitions.Def_SybilClinch_demandX
-- name    : SybilClinch_demandX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:42:01.330537+00:00
-- url     : https://prove2.me/theorems/ebe352b1-fe88-43f3-bcc3-96be064ab5b9
-- title:
--   Sell-$X$ side $D_X=\sum_{E_X}r_i$
-- statement:
--   In units of $X$, the sell-$X$ side is $D_X:=\sum_{i\in E_X}r_i$. The minority fill is $M=\min\{D_Y,D_X\}$; if $D_Y=D_X$, sell-$X$ is designated the minority.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.1, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_SybilClinch_eligX

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.1, printed p.25 (PDF p.27): the sell-`X` side in units of `X`,
`D_X := Σ_{i ∈ E_X} rᵢ`. -/
noncomputable def demandX (A : AdmissibleAMM) (ids : Finset ℕ) (rep : ℕ → Report) : ℝ :=
  ∑ i ∈ eligX A ids rep, (rep i).bud

end SybilClinch


