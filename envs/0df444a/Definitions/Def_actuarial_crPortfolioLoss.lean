-- Prove2me | Definitions.Def_actuarial_crPortfolioLoss
-- name    : actuarial_crPortfolioLoss
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:32.032992+00:00
-- url     : https://prove2.me/theorems/95a73c9d-c9e4-4cd6-bfa7-8ea03d32cf03
-- title:
--   Coherent worst-case actuarial premium and portfolio: crPortfolioLoss
-- statement:
--   Total monetary loss of two insurance portfolios on a common underlying finite scenario space; dependence is retained by shared outcome i.
--
--   Mathematical relation:
--
--   $$
--   X i+Y i
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def crPortfolioLoss {n : ℕ} (X Y : Fin n→ℝ) (i : Fin n) : ℝ := X i+Y i

end ActuarialValuation


