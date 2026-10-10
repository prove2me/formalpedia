-- Prove2me | Definitions.Def_actuarial_mackProjection
-- name    : actuarial_mackProjection
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:04:55.067022+00:00
-- url     : https://prove2.me/theorems/832f3822-9c1c-4c4b-a0e0-5771d88d2a82
-- title:
--   Development factors and volume-weighted exposure: mackProjection
-- statement:
--   One-step predicted cumulative losses multiply current losses by a selected development ratio. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \widehat C_{j+1}=C_jf_j
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 213. Thomas Mack (1993), Distribution-free Calculation of the Standard Error of Chain Ladder Reserve Estimates, ASTIN Bulletin 23(2), pp. 213-225, https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf; Thomas Mack (1999), The Standard Error of Chain Ladder Reserve Estimates: Recursive Calculation and Inclusion of a Tail Factor, https://www.casact.org/sites/default/files/database/astin_vol29no2_361.pdf. Parent topic: Mack claims reserving uncertainty, finite conditional development factor moments, process variance and estimation uncertainty. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def mackProjection (current factor : ℝ) : ℝ := current * factor

end ActuarialValuation


