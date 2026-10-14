-- Prove2me | Definitions.Def_actuarial_d_annPath
-- name    : actuarial_d_annPath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:33:49.762654+00:00
-- url     : https://prove2.me/theorems/0392c0ea-6566-4106-9dc4-a2e59c875f68
-- title:
--   Realised timed-annuity cashflow
-- statement:
--   Realised timed-annuity cashflow. Discounted payment stream at commencement-anniversary ticks, with an explicit state indicator. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   Z_{\text{ann}}(i,j)=\sum_{t=0}^{n-1}d_tb_t I_{ij}(t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialJointD
noncomputable def annPath (n : ℕ) (d b : ℕ → ℝ) (s : ℕ → ℝ) : ℝ := ∑ t ∈ Finset.range n, d t * b t * s t
end ActuarialJointD


