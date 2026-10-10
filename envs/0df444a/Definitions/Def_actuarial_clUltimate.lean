-- Prove2me | Definitions.Def_actuarial_clUltimate
-- name    : actuarial_clUltimate
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T07:12:43.675539+00:00
-- url     : https://prove2.me/theorems/f27271e3-24b7-4392-b987-8bc303a1312e
-- title:
--   Development to ultimate and outstanding reserve: clUltimate
-- statement:
--   Ultimate paid claims are the latest cumulative observed payments multiplied by the selected age-to-ultimate factor. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   U=CF
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def clUltimate (latest factor : ℝ) : ℝ := latest * factor

end ActuarialValuation


