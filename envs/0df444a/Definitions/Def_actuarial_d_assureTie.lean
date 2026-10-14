-- Prove2me | Definitions.Def_actuarial_d_assureTie
-- name    : actuarial_d_assureTie
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-13T06:38:04.040268+00:00
-- url     : https://prove2.me/theorems/03e7508b-1538-405a-bc85-ac77988c4d87
-- title:
--   Simultaneous-death assurance
-- statement:
--   Simultaneous-death assurance. Expected discount factor of the actual order-sensitive death settlement. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   A_{\text{tie}}=\sum_{i,j}p_{ij}C_{\text{tie}}(i,j)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.8, p. 153. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_tiePath

namespace ActuarialJointD
noncomputable def assureTie (h : ℕ) (p : ℕ → ℕ → ℝ) (d : ℕ → ℝ) : ℝ := expect h p (fun i j => tiePath h d i j)
end ActuarialJointD


