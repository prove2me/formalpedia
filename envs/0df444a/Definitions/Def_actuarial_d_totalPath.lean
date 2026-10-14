-- Prove2me | Definitions.Def_actuarial_d_totalPath
-- name    : actuarial_d_totalPath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:39:49.558979+00:00
-- url     : https://prove2.me/theorems/1c4d94a2-bcb7-4dbd-9890-f9a94ed43994
-- title:
--   Realised joint-and-survivor cashflow
-- statement:
--   Realised joint-and-survivor cashflow. A full member pension, a spouse reversion, first and second death claims and separate strict-order and tie riders. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   Z_{\text{total}}=Z_{\text{member}}+\rho Z_{\text{reversion}}+Z_{\text{death riders}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_annPath
import Definitions.Def_actuarial_d_firstPath
import Definitions.Def_actuarial_d_secondPath
import Definitions.Def_actuarial_d_xFirstPath
import Definitions.Def_actuarial_d_yFirstPath
import Definitions.Def_actuarial_d_tiePath

namespace ActuarialJointD
noncomputable def totalPath (h n : ℕ) (d b : ℕ → ℝ) (rho f s fx fy ft : ℝ) (i j : ℕ) : ℝ := annPath n d b (fun t => alive i t + rho * onlyY i j t) + f * firstPath h d i j + s * secondPath h d i j + fx * xFirstPath h d i j + fy * yFirstPath h d i j + ft * tiePath h d i j
end ActuarialJointD


