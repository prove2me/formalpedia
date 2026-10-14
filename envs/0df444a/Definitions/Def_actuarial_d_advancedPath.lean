-- Prove2me | Definitions.Def_actuarial_d_advancedPath
-- name    : actuarial_d_advancedPath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:53:07.743594+00:00
-- url     : https://prove2.me/theorems/91a88a85-63b5-4dbc-ba7b-3865c668b0d6
-- title:
--   Advanced realised member-and-spouse contract
-- statement:
--   Advanced realised member-and-spouse contract. Combines deferred instalments, a guaranteed member stream, blocked spouse reversion and order-sensitive death riders. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   Z_{\text{advanced}}=Z_{\text{deferred guarantee}}+\rho Z_{\text{delayed spouse}}+Z_{\text{death riders}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_firstPath
import Definitions.Def_actuarial_d_secondPath
import Definitions.Def_actuarial_d_xFirstPath
import Definitions.Def_actuarial_d_yFirstPath
import Definitions.Def_actuarial_d_tiePath
import Definitions.Def_actuarial_d_annRange
import Definitions.Def_actuarial_d_guaranteeMember
import Definitions.Def_actuarial_d_delayedSpouse

namespace ActuarialJointD
noncomputable def advancedPath (h a n g : ℕ) (d b : ℕ → ℝ) (rho f s fx fy ft : ℝ) (i j : ℕ) : ℝ := annRange a n d b (fun t => guaranteeMember g i t + rho * delayedSpouse g i j t) + f * firstPath h d i j + s * secondPath h d i j + fx * xFirstPath h d i j + fy * yFirstPath h d i j + ft * tiePath h d i j
end ActuarialJointD


