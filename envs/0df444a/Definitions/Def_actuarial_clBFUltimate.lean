-- Prove2me | Definitions.Def_actuarial_clBFUltimate
-- name    : actuarial_clBFUltimate
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T07:24:36.962564+00:00
-- url     : https://prove2.me/theorems/405175e6-1957-4dfd-a228-1e04bd7cca8d
-- title:
--   Prior expected ultimate and Bornhuetter-Ferguson reconciliation: clBFUltimate
-- statement:
--   Bornhuetter-Ferguson ultimate combines the observed paid amount with expected future emergence. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   U_{BF}=C+E(1-1/F)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clBFReserve

namespace ActuarialValuation

noncomputable def clBFUltimate (latest expected factor : ℝ) : ℝ := latest + clBFReserve expected factor

end ActuarialValuation


