-- Prove2me | Definitions.Def_actuarial_mackSquaredResidual
-- name    : actuarial_mackSquaredResidual
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:05:00.95224+00:00
-- url     : https://prove2.me/theorems/7acd305a-b76a-4a28-8d4c-e7113f0a1900
-- title:
--   Residual dispersion and one-step uncertainty: mackSquaredResidual
-- statement:
--   Squared observed-versus-predicted cumulative claims error is the sample dispersion contribution. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   e^2=(C_{j+1}-f_jC_j)^2
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 213. Thomas Mack (1993), Distribution-free Calculation of the Standard Error of Chain Ladder Reserve Estimates, ASTIN Bulletin 23(2), pp. 213-225, https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf; Thomas Mack (1999), The Standard Error of Chain Ladder Reserve Estimates: Recursive Calculation and Inclusion of a Tail Factor, https://www.casact.org/sites/default/files/database/astin_vol29no2_361.pdf. Parent topic: Mack claims reserving uncertainty, finite conditional development factor moments, process variance and estimation uncertainty. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def mackSquaredResidual (actual predicted : ℝ) : ℝ := (actual - predicted)^2

end ActuarialValuation


