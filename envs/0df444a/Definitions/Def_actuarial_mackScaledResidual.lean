-- Prove2me | Definitions.Def_actuarial_mackScaledResidual
-- name    : actuarial_mackScaledResidual
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:05:13.110173+00:00
-- url     : https://prove2.me/theorems/aeb743c7-deb0-45e1-b170-8afbfe074fef
-- title:
--   Residual dispersion and one-step uncertainty: mackScaledResidual
-- statement:
--   Mack's development-scale residual uses positive cumulative paid claims as the denominator. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   z_i=e_i^2/C_{i,j}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 213. Thomas Mack (1993), Distribution-free Calculation of the Standard Error of Chain Ladder Reserve Estimates, ASTIN Bulletin 23(2), pp. 213-225, https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf; Thomas Mack (1999), The Standard Error of Chain Ladder Reserve Estimates: Recursive Calculation and Inclusion of a Tail Factor, https://www.casact.org/sites/default/files/database/astin_vol29no2_361.pdf. Parent topic: Mack claims reserving uncertainty, finite conditional development factor moments, process variance and estimation uncertainty. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackSquaredResidual

namespace ActuarialValuation

noncomputable def mackScaledResidual (actual predicted exposure : ℝ) : ℝ := mackSquaredResidual actual predicted / exposure

end ActuarialValuation


