-- Prove2me | Definitions.Def_SybilClinch_AdmissibleAMM_Ctil
-- name    : SybilClinch_AdmissibleAMM_Ctil
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:39:51.800053+00:00
-- url     : https://prove2.me/theorems/9ad1ac77-8874-4601-a898-6ccd072b420a
-- title:
--   Extended cost $\widetilde C_M$
-- statement:
--   When sell-$Y$ is dominant with minority fill $M$, the dominant auction faces the extended cost
--   $$\widetilde C_M(z):=\begin{cases}p_0z,&0\le z\le M,\\ p_0M+C(z-M),&M\le z<M+x_0.\end{cases}\qquad(57)$$
--   The first $M$ units cost $p_0$ each and represent the sell-$X$ minority orders; further output costs the original pool cost.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.2, (57), p.26 (PDF p.28)

import Mathlib
import Definitions.Def_SybilClinch_AdmissibleAMM_C
import Definitions.Def_SybilClinch_AdmissibleAMM_p0

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.2, (57), printed p.26 (PDF p.28): the extended cost faced by the dominant sell-`Y`
auction, `C̃_M(z) := p₀z` for `0 ≤ z ≤ M` and `p₀M + C(z − M)` for `M ≤ z < M + x₀`. -/
noncomputable def AdmissibleAMM.Ctil (A : AdmissibleAMM) (M z : ℝ) : ℝ :=
  if z ≤ M then A.p0 * z else A.p0 * M + A.C (z - M)

end SybilClinch


