-- Prove2me | Definitions.Def_actuarial_d_mthlyPath
-- name    : actuarial_d_mthlyPath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:49:04.170361+00:00
-- url     : https://prove2.me/theorems/22a2356d-1845-4817-ad42-c495bb21361b
-- title:
--   m-thly annuity-due path
-- statement:
--   m-thly annuity-due path. Subannual times are indexed by m ticks per year. b is an annual rate, each instalment b/m, with m positive. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   Z^{(m)}=\sum_{k=0}^{ym-1}d_k\frac{b_k}{m}I_{ij}(k),\quad m>0
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialJointD
noncomputable def mthlyPath (years m : ℕ) (d b : ℕ → ℝ) (s : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range (years*m), d k * (b k / (m : ℝ)) * s k
end ActuarialJointD


