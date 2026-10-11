-- Prove2me | Definitions.Def_actuarial_crStopLossPremium
-- name    : actuarial_crStopLossPremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:32:01.535119+00:00
-- url     : https://prove2.me/theorems/50c3c14a-502b-4e54-9f1b-25a0c49d6242
-- title:
--   Stop-loss risk comparison and limitations of floored risk principles: crStopLossPremium
-- statement:
--   Expected cash amount insurer pays under an exact finite stop-loss insurance contract at deductible d.
--
--   Mathematical relation:
--
--   $$
--   crStopLoss p X deductible
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crStopLoss

namespace ActuarialValuation

noncomputable def crStopLossPremium {n : ℕ} (p X : Fin n→ℝ) (deductible : ℝ) : ℝ := crStopLoss p X deductible

end ActuarialValuation


