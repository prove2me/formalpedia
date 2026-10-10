-- Prove2me | Definitions.Def_actuarial_clLinkDenominator
-- name    : actuarial_clLinkDenominator
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T07:11:02.549635+00:00
-- url     : https://prove2.me/theorems/f976c8d0-32ff-4764-b823-f3e9791e47bf
-- title:
--   Cumulative triangles and selected development factors: clLinkDenominator
-- statement:
--   Only consistently observed origin cohorts are included in both link factor sums. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   D_j=\sum_{i<m}C_{i,j}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def clLinkDenominator (paid : ℕ → ℕ → ℝ) (m j : ℕ) : ℝ := ∑ i ∈ Finset.range m, paid i j

end ActuarialValuation


