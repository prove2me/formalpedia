-- Prove2me | Definitions.Def_actuarial_mackProcessVariance
-- name    : actuarial_mackProcessVariance
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:06:13.250974+00:00
-- url     : https://prove2.me/theorems/eacbd24a-7298-4e4d-8284-eff5f0ecef52
-- title:
--   Process error, estimation error and reserve variance: mackProcessVariance
-- statement:
--   One-step conditional process variance scales with current cumulative claims in Mack's model. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   v_{proc}=\sigma_j^2C_j
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 213. Thomas Mack (1993), Distribution-free Calculation of the Standard Error of Chain Ladder Reserve Estimates, ASTIN Bulletin 23(2), pp. 213-225, https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf; Thomas Mack (1999), The Standard Error of Chain Ladder Reserve Estimates: Recursive Calculation and Inclusion of a Tail Factor, https://www.casact.org/sites/default/files/database/astin_vol29no2_361.pdf. Parent topic: Mack claims reserving uncertainty, finite conditional development factor moments, process variance and estimation uncertainty. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def mackProcessVariance (sigma2 current : ℝ) : ℝ := sigma2 * current

end ActuarialValuation


