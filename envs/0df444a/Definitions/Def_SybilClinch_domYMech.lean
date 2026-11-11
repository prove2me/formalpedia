-- Prove2me | Definitions.Def_SybilClinch_domYMech
-- name    : SybilClinch_domYMech
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:42:54.660241+00:00
-- url     : https://prove2.me/theorems/c14f1045-31d3-481e-afb8-51a9afc58233
-- title:
--   Dominant sell-$Y$ auction on $\widetilde C_M$
-- statement:
--   When $D_Y\ge D_X$, the dominant auction is the one-sided mechanism with $(C,T^{\rm amm},x_0)$ replaced by $(\widetilde C_M,\widetilde T_M,M+x_0)$, $M=D_X$, and the clock starting at $p_0$.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.2, rule 2, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_SybilClinch_chordMech
import Definitions.Def_SybilClinch_AdmissibleAMM_Ctil
import Definitions.Def_SybilClinch_demandX

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.2, rule 2, printed p.26 (PDF p.28): the dominant sell-`Y` auction when `D_Y ≥ D_X`:
the one-sided mechanism with `(C, T^amm, x₀)` replaced by `(C̃_M, T̃_M, M + x₀)`, `M = D_X`, clock
starting at `p₀`. -/
noncomputable def domYMech (A : AdmissibleAMM) (ids : Finset ℕ) (rep : ℕ → Report) : TargetMech :=
  chordMech (A.Ctil (demandX A ids rep)) A.p0 (demandX A ids rep + A.x0)

end SybilClinch


