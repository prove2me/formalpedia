-- Prove2me | Definitions.Def_actuarial_d_annRange
-- name    : actuarial_d_annRange
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:40:22.185695+00:00
-- url     : https://prove2.me/theorems/e7e0c1dc-2f68-4773-b354-2d6010c3d8ab
-- title:
--   Deferred temporary realised annuity
-- statement:
--   Deferred temporary realised annuity. Discount and benefit at actual payment date a+k, including the first eligible date. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   Z_{a,n}(i,j)=\sum_{k=0}^{n-1}d_{a+k}b_{a+k}I_{ij}(a+k)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialJointD
noncomputable def annRange (a n : ℕ) (d b : ℕ → ℝ) (s : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range n, d (a+k) * b (a+k) * s (a+k)
end ActuarialJointD


