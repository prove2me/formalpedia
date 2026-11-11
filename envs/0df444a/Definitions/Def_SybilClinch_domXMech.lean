-- Prove2me | Definitions.Def_SybilClinch_domXMech
-- name    : SybilClinch_domXMech
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:42:50.091425+00:00
-- url     : https://prove2.me/theorems/7ab2f4ea-997b-41fc-bcce-b77b64a1829b
-- title:
--   Reverse auction on $\widetilde C^{\rm rev}_M$
-- statement:
--   When $D_Y<D_X$, the reverse auction is the one-sided mechanism with cost $\widetilde C^{\rm rev}_M$, target $\widetilde T^{\rm rev}_M$, capacity $p_0M+y_0$, $M=D_Y$, and clock $p^{\rm rev}$ (units of $X$ per unit of $Y$) starting at $1/p_0$.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.2, pp.26–27 (PDF pp.28–29)

import Mathlib
import Definitions.Def_SybilClinch_chordMech
import Definitions.Def_SybilClinch_AdmissibleAMM_CtilRev
import Definitions.Def_SybilClinch_demandY

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.2, printed pp.26–27 (PDF pp.28–29): the reverse auction when `D_Y < D_X`: the one-sided
mechanism with cost `C̃^rev_M`, target `T̃^rev_M`, capacity `p₀M + y₀`, `M = D_Y`, clock `p^rev`
starting at `1/p₀`. -/
noncomputable def domXMech (A : AdmissibleAMM) (ids : Finset ℕ) (rep : ℕ → Report) : TargetMech :=
  chordMech (A.CtilRev (demandY A ids rep)) A.p0⁻¹ (A.p0 * demandY A ids rep + A.y0)

end SybilClinch


