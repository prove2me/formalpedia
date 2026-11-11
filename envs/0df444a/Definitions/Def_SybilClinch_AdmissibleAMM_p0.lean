-- Prove2me | Definitions.Def_SybilClinch_AdmissibleAMM_p0
-- name    : SybilClinch_AdmissibleAMM_p0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:37:49.324582+00:00
-- url     : https://prove2.me/theorems/a578ab89-a8d4-41f8-9182-e7702555516c
-- title:
--   Spot price $p_0=-\varphi'(x_0)$
-- statement:
--   The spot price of one unit of $X$, measured in units of $Y$, is
--   $$p_0:=-\varphi'(x_0).$$
--   It is the initial marginal exchange rate of the pool and the eligibility threshold of the mechanism: sell-$Y$ orders with value at least $p_0$ and sell-$X$ orders with value at most $p_0$ are eligible.
--
--   **Formalization Note** The derivative exists because $\varphi$ is differentiable at $x_0$.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2, Definition 2.1, p.4 (PDF p.6)

import Mathlib
import Definitions.Def_SybilClinch_AdmissibleAMM

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2, Definition 2.1, printed p.4 (PDF p.6): the spot price of one unit of `X` in units of
`Y`, `p₀ := −φ′(x₀)`.

**Formalization Note.** `deriv` is meaningful because `φ` is differentiable at `x₀` (a field of
`AdmissibleAMM`). -/
noncomputable def AdmissibleAMM.p0 (A : AdmissibleAMM) : ℝ := - deriv A.φ A.x0

end SybilClinch


