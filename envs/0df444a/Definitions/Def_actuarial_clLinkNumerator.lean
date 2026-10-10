-- Prove2me | Definitions.Def_actuarial_clLinkNumerator
-- name    : actuarial_clLinkNumerator
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T07:10:53.630993+00:00
-- url     : https://prove2.me/theorems/040d7c34-7cdb-440a-906e-43b044bd1dc3
-- title:
--   Cumulative triangles and selected development factors: clLinkNumerator
-- statement:
--   All selected origin cohorts contribute the next development-age amounts to the common-ratio numerator. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   N_j=\sum_{i<m}C_{i,j+1}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def clLinkNumerator (paid : ℕ → ℕ → ℝ) (m j : ℕ) : ℝ := ∑ i ∈ Finset.range m, paid i (j+1)

end ActuarialValuation


