-- Prove2me | Definitions.Def_actuarial_mackDenominator
-- name    : actuarial_mackDenominator
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:04:36.656988+00:00
-- url     : https://prove2.me/theorems/f2cdfe49-de59-4635-8026-e293de3f2944
-- title:
--   Development factors and volume-weighted exposure: mackDenominator
-- statement:
--   The denominator must refer to the same cohort exposure as the numerator. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   D_j=\sum_i C_{i,j}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 213. Thomas Mack (1993), Distribution-free Calculation of the Standard Error of Chain Ladder Reserve Estimates, ASTIN Bulletin 23(2), pp. 213-225, https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf; Thomas Mack (1999), The Standard Error of Chain Ladder Reserve Estimates: Recursive Calculation and Inclusion of a Tail Factor, https://www.casact.org/sites/default/files/database/astin_vol29no2_361.pdf. Parent topic: Mack claims reserving uncertainty, finite conditional development factor moments, process variance and estimation uncertainty. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def mackDenominator (c : ℕ → ℕ → ℝ) (m j : ℕ) : ℝ := ∑ i ∈ Finset.range m, c i j

end ActuarialValuation


