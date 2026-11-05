-- Prove2me | Definitions.Def_TwoWayCVQKD_cloner
-- name    : TwoWayCVQKD_cloner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:41.866393+00:00
-- url     : https://prove2.me/theorems/1e2ddfde-557d-412f-9a0d-f741d518c2ac
-- title:
--   Beam splitter of the entangling cloner
-- statement:
--   An entangling cloner of transmission $T$ mixes a signal mode $A$ with one mode $E$ of Eve's EPR pair on a beam splitter. On each quadrature,
--   $$
--   \hat B=\sqrt T\,\hat A+\sqrt{1-T}\,\hat E,\qquad \hat E'=\sqrt T\,\hat E-\sqrt{1-T}\,\hat A,
--   $$
--   where $B$ continues along the channel and $E'$ goes to Eve.
--
--   **Formalization Note** The paper does not print the signs of the beam splitter. This sign choice reproduces its covariance entries $\mu=(W-V)[(1-T)T]^{1/2}$ of Eq. (19) and $\mu'$, $\theta'$ of Eq. (51).
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, p.2 and p.7 (entangling cloner), with Eqs. (19), (51)

import Mathlib

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, p.2 and p.7: the beam splitter
of transmission `T` of an entangling cloner, mixing a signal quadrature `a` and Eve's quadrature
`e`. The first output is the transmitted one `√T a + √(1 - T) e`, the second is Eve's
`√T e - √(1 - T) a`.

**Formalization Note** The paper does not print the beam-splitter signs. This choice reproduces its
`μ = (W - V)[(1 - T)T]^{1/2}` of Eq. (19) and `μ'`, `θ'` of Eq. (51). Quadratures are coefficient
vectors over the sources (`crossCov`). -/
noncomputable def cloner {S : Type*} (T : ℝ) (a e : S → ℝ) : (S → ℝ) × (S → ℝ) :=
  (Real.sqrt T • a + Real.sqrt (1 - T) • e, Real.sqrt T • e - Real.sqrt (1 - T) • a)

end TwoWayCVQKD


