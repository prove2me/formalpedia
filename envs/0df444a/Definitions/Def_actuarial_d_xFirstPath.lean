-- Prove2me | Definitions.Def_actuarial_d_xFirstPath
-- name    : actuarial_d_xFirstPath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:36:24.148549+00:00
-- url     : https://prove2.me/theorems/ed343d26-abc6-4089-be5d-de084a13071f
-- title:
--   Member dies first
-- statement:
--   Member dies first. Strict death-order contingent lump sum to the specified recipient. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   C_{x\prec y}(i,j)=d_{i+1}\mathbf{1}_{\{i<j,\ i<h\}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.8.1, p. 153. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialJointD
noncomputable def xFirstPath (h : ℕ) (d : ℕ → ℝ) (i j : ℕ) : ℝ := if i < j ∧ i < h then d (i+1) else 0
end ActuarialJointD


