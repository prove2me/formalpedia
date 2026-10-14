-- Prove2me | Definitions.Def_actuarial_d_alive
-- name    : actuarial_d_alive
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:30:46.999532+00:00
-- url     : https://prove2.me/theorems/a91b7884-a090-4090-983e-06c2c8139437
-- title:
--   Alive at an anniversary
-- statement:
--   Alive at an anniversary. Death-year state i survives all payment anniversaries t at or before i. The final index h means right censoring. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   I_x(i,t)=\mathbf{1}_{\{t\leq i\}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialJointD
noncomputable def alive (i t : ℕ) : ℝ := if t ≤ i then (1 : ℝ) else 0
end ActuarialJointD


