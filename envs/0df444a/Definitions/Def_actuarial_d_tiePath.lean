-- Prove2me | Definitions.Def_actuarial_d_tiePath
-- name    : actuarial_d_tiePath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:36:39.31888+00:00
-- url     : https://prove2.me/theorems/34a5fe28-1760-49d7-83dd-e95530d3c5e6
-- title:
--   Simultaneous-grid death
-- statement:
--   Simultaneous-grid death. Joint law's equal-tick death event, with separate entitlement and claim timing. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   C_{\text{tie}}(i,j)=d_{i+1}\mathbf{1}_{\{i=j<h\}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.8, p. 153. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialJointD
noncomputable def tiePath (h : ℕ) (d : ℕ → ℝ) (i j : ℕ) : ℝ := if i = j ∧ i < h then d (i+1) else 0
end ActuarialJointD


