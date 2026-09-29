-- Prove2me | Definitions.Def_mme_CW_auxiliary_RHS_coupled
-- name    : mme_CW_auxiliary_RHS_coupled
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T05:27:50.480492+00:00
-- url     : https://prove2.me/theorems/f6dd112c-c39a-46b5-9cf3-d5c35497b4f8
-- title:
--   CW Section 8 auxiliary expression with a free coupled base
-- statement:
--   For tensor-square profile frequencies $a,b,c,d$, the Coppersmith--Winograd Section 8 expression receives three non-coupled block contributions and one cyclic coupled contribution. If $C$ denotes an attained cyclic coupled tau-value base, define
--
--   $$
--   B_C(q,\tau,a,b,c,d)=
--   \frac{(2q)^{6\tau b}(q^2+2)^{3\tau c}C^d}
--    {(2a+2b+c)^{2a+2b+c}(2b+2d)^{2b+2d}
--     (2c+d)^{2c+d}(2b)^{2b}a^a}.
--   $$
--
--   Substituting the raw coupled boundary base
--
--   $$
--   C=4q^{3\tau}(q^{3\tau}+2)
--   $$
--
--   recovers the existing Section 8 expression. Exposing $C$ is necessary for a rate-correct formalization: the coupled construction attains every strict sub-bound and approaches the raw boundary, but Stirling and Salem--Spencer losses do not imply constant-relative attainment at the boundary itself.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), tensor-square constituent values and Section 8 auxiliary expression on journal pp. 266--269 (PDF pp. 16--19), especially equations (12)--(13); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_auxiliary_RHS

namespace MME

noncomputable def auxiliaryRHSWithCoupled
    (q : ℕ) (tau a b c d coupledBase : ℝ) : ℝ :=
  ((2 * (q : ℝ)) ^ (6 * tau * b) *
      ((q : ℝ) ^ 2 + 2) ^ (3 * tau * c) *
      coupledBase ^ d) /
    ((2 * a + 2 * b + c) ^ (2 * a + 2 * b + c) *
      (2 * b + 2 * d) ^ (2 * b + 2 * d) *
      (2 * c + d) ^ (2 * c + d) *
      (2 * b) ^ (2 * b) * a ^ a)

end MME


