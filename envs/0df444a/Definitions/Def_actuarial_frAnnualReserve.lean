-- Prove2me | Definitions.Def_actuarial_frAnnualReserve
-- name    : actuarial_frAnnualReserve
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:14:57.572867+00:00
-- url     : https://prove2.me/theorems/233a45ca-b481-4044-bcfb-0cc4ffe97c4c
-- title:
--   Fractional premiums and policy reserves: frAnnualReserve
-- statement:
--   Year-end policy reserve conditional on survival to the next anniversary, with benefit paid at the year end and premium at the previous anniversary.
--
--   Mathematical relation:
--
--   $$
--   ((assets+premium)*growth-q*benefit)/(1-q)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def frAnnualReserve (assets premium benefit q growth : ℝ) : ℝ := ((assets+premium)*growth-q*benefit)/(1-q)

end ActuarialValuation


