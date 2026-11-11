-- Prove2me | Definitions.Def_SybilClinch_AdmissibleAMM_CtilRev
-- name    : SybilClinch_AdmissibleAMM_CtilRev
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:40:12.968198+00:00
-- url     : https://prove2.me/theorems/8b9609bb-5663-4263-bedb-04203b7bcaf0
-- title:
--   Extended reverse cost $\widetilde C^{\rm rev}_M$
-- statement:
--   When sell-$X$ is dominant with minority fill $M$, the reverse auction faces, in units of $X$ needed to release $w$ units of $Y$,
--   $$\widetilde C^{\rm rev}_M(w):=\begin{cases}w/p_0,&0\le w\le p_0M,\\ M+C^{\rm rev}(w-p_0M),&p_0M\le w<p_0M+y_0.\end{cases}$$
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.2, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_SybilClinch_AdmissibleAMM_Crev
import Definitions.Def_SybilClinch_AdmissibleAMM_p0

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.2, printed p.26 (PDF p.28): the extended reverse cost, in units of `X` needed to release
`w` units of `Y`: `C̃^rev_M(w) := w/p₀` for `0 ≤ w ≤ p₀M` and `M + C^rev(w − p₀M)` for
`p₀M ≤ w < p₀M + y₀`. -/
noncomputable def AdmissibleAMM.CtilRev (A : AdmissibleAMM) (M w : ℝ) : ℝ :=
  if w ≤ A.p0 * M then w / A.p0 else M + A.Crev (w - A.p0 * M)

end SybilClinch


