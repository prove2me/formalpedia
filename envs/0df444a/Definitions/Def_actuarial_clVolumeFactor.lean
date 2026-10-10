-- Prove2me | Definitions.Def_actuarial_clVolumeFactor
-- name    : actuarial_clVolumeFactor
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T07:11:15.027742+00:00
-- url     : https://prove2.me/theorems/5cb1aab7-1427-4545-89d5-05b274ffe748
-- title:
--   Cumulative triangles and selected development factors: clVolumeFactor
-- statement:
--   Selected age-to-age development factor is the volume-weighted ratio rather than an unweighted mean of individual link ratios. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   f_j=N_j/D_j
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clLinkNumerator
import Definitions.Def_actuarial_clLinkDenominator

namespace ActuarialValuation

noncomputable def clVolumeFactor (paid : ℕ → ℕ → ℝ) (m j : ℕ) : ℝ := clLinkNumerator paid m j / clLinkDenominator paid m j

end ActuarialValuation


