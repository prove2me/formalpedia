-- Prove2me | Definitions.Def_actuarial_d_annValue
-- name    : actuarial_d_annValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:34:02.198972+00:00
-- url     : https://prove2.me/theorems/2e20d081-59b1-44f0-b1c8-b83e5e910dd7
-- title:
--   Joint occupation annuity EPV
-- statement:
--   Joint occupation annuity EPV. Average of realised discounted annuity streams over all joint mortality states. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V_{\text{ann}}=\sum_{i,j}p_{ij}\sum_{t=0}^{n-1}d_tb_t I_{ij}(t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_annPath

namespace ActuarialJointD
noncomputable def annValue (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (s : ℕ → ℕ → ℕ → ℝ) : ℝ := expect h p (fun i j => annPath n d b (s i j))
end ActuarialJointD


