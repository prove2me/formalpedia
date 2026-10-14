-- Prove2me | Definitions.Def_actuarial_d_arrearsValue
-- name    : actuarial_d_arrearsValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:47:24.38924+00:00
-- url     : https://prove2.me/theorems/14ae8f71-07ee-479e-96d4-f559291450fd
-- title:
--   Arrears occupation EPV
-- statement:
--   Arrears occupation EPV. Averages post-year survival contingent actual payments, distinct from annuity-due. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V_{\text{arrears}}=\mathbb E_p[Z_{\text{arrears}}]
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_arrearsPath

namespace ActuarialJointD
noncomputable def arrearsValue (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (s : ℕ → ℕ → ℕ → ℝ) : ℝ := expect h p (fun i j => arrearsPath n d b (s i j))
end ActuarialJointD


