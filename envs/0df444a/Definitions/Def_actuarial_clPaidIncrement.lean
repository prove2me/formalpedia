-- Prove2me | Definitions.Def_actuarial_clPaidIncrement
-- name    : actuarial_clPaidIncrement
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T07:10:48.430987+00:00
-- url     : https://prove2.me/theorems/21a82965-2917-4aa8-bb34-f98b2ff0421d
-- title:
--   Cumulative triangles and selected development factors: clPaidIncrement
-- statement:
--   An incremental claim payment is the difference of successive cumulative paid amounts, not a second independent cumulative amount. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   I_{i,j+1}=C_{i,j+1}-C_{i,j}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def clPaidIncrement (paid : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ := paid i (j+1) - paid i j

end ActuarialValuation


