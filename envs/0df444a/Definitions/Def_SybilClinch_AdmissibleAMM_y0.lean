-- Prove2me | Definitions.Def_SybilClinch_AdmissibleAMM_y0
-- name    : SybilClinch_AdmissibleAMM_y0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:37:46.424463+00:00
-- url     : https://prove2.me/theorems/660aa327-c8dc-4ad3-9a2c-8fa0a43a0943
-- title:
--   Initial $Y$ reserve $y_0=\varphi(x_0)$
-- statement:
--   For an admissible AMM with reserve curve $\varphi$ and initial $X$ reserve $x_0$, the initial $Y$ reserve is $y_0:=\varphi(x_0)>0$, so the initial state $(x_0,y_0)$ lies on the reserve curve.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2, Definition 2.1, p.4 (PDF p.6)

import Mathlib
import Definitions.Def_SybilClinch_AdmissibleAMM

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2, Definition 2.1, printed p.4 (PDF p.6): the initial `Y` reserve `y₀ = φ(x₀)`. -/
def AdmissibleAMM.y0 (A : AdmissibleAMM) : ℝ := A.φ A.x0

end SybilClinch


