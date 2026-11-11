-- Prove2me | Definitions.Def_SybilClinch_AdmissibleAMM_C
-- name    : SybilClinch_AdmissibleAMM_C
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:38:44.180692+00:00
-- url     : https://prove2.me/theorems/e28338e4-c2d9-4119-a3e1-5f8b76fe7936
-- title:
--   Signed pool cost $C(z)=\varphi(x_0-z)-y_0$
-- statement:
--   For a net release $z<x_0$ of asset $X$ by the pool, the signed pool cost is
--   $$C(z):=\varphi(x_0-z)-y_0 ,$$
--   the net amount of $Y$ the pool must receive. Here $z>0$ means the pool releases $z$ units of $X$ and $z<0$ that it absorbs $-z$ units; $C(z)$ may be negative. $C$ is continuous, strictly increasing and convex with $C(0)=0$, $C(z)\to\infty$ as $z\uparrow x_0$ and $C'(0)=p_0$.
--
--   **Formalization Note** Total function; only $z<x_0$ is meaningful.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_SybilClinch_AdmissibleAMM_y0

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2, printed p.5 (PDF p.7): the signed pool cost of a net release `z < x₀` of asset `X`,
`C(z) := φ(x₀ − z) − y₀` (units of `Y` received by the pool; negative when the pool pays `Y`).

**Formalization Note.** Total function; only `z < x₀` is meaningful (there `x₀ − z > 0`). -/
def AdmissibleAMM.C (A : AdmissibleAMM) (z : ℝ) : ℝ := A.φ (A.x0 - z) - A.y0

end SybilClinch


