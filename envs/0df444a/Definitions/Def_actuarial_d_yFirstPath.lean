-- Prove2me | Definitions.Def_actuarial_d_yFirstPath
-- name    : actuarial_d_yFirstPath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:36:31.824405+00:00
-- url     : https://prove2.me/theorems/db9ba487-5ed2-4238-bddc-269e809d1d9e
-- title:
--   Spouse dies first
-- statement:
--   Spouse dies first. Strict reversed-order contingent lump sum. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   C_{y\prec x}(i,j)=d_{j+1}\mathbf{1}_{\{j<i,\ j<h\}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.8.1, p. 153. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialJointD
noncomputable def yFirstPath (h : ℕ) (d : ℕ → ℝ) (i j : ℕ) : ℝ := if j < i ∧ j < h then d (j+1) else 0
end ActuarialJointD


