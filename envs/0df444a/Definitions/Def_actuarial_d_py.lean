-- Prove2me | Definitions.Def_actuarial_d_py
-- name    : actuarial_d_py
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:33:01.452323+00:00
-- url     : https://prove2.me/theorems/58f397ef-e3c5-45e9-bee0-09b41ae374f6
-- title:
--   Spouse marginal survival
-- statement:
--   Spouse marginal survival. Spouse survival calculated from the same underlying joint law. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   S_y(t)=\sum_{i,j}p_{ij}\mathbf{1}_{\{t\leq j\}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_expect

namespace ActuarialJointD
noncomputable def py (h : ℕ) (p : ℕ → ℕ → ℝ) (t : ℕ) : ℝ := expect h p (fun i j => alive j t)
end ActuarialJointD


