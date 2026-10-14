-- Prove2me | Definitions.Def_actuarial_d_arrearsPath
-- name    : actuarial_d_arrearsPath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:47:12.437574+00:00
-- url     : https://prove2.me/theorems/d43ac8bf-4d2e-4001-9f10-81e25dbd6d0c
-- title:
--   Realised annuity in arrears
-- statement:
--   Realised annuity in arrears. Instalments at dates 1 to n, with survival checked at their actual payment dates. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   Z_{\text{arrears}}=\sum_{k=0}^{n-1}d_{k+1}b_{k+1}I_{ij}(k+1)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialJointD
noncomputable def arrearsPath (n : ℕ) (d b : ℕ → ℝ) (s : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range n, d (k+1) * b (k+1) * s (k+1)
end ActuarialJointD


