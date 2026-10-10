-- Prove2me | Definitions.Def_actuarial_mackVarianceNumerator
-- name    : actuarial_mackVarianceNumerator
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:05:30.283228+00:00
-- url     : https://prove2.me/theorems/49f5ac47-c6bf-4359-908c-dd74096cd307
-- title:
--   Residual dispersion and one-step uncertainty: mackVarianceNumerator
-- statement:
--   The total weighted squared residual quantity accumulates observed deviations over common cohorts. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   V=\sum_i e_i^2/C_i
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 213. Thomas Mack (1993), Distribution-free Calculation of the Standard Error of Chain Ladder Reserve Estimates, ASTIN Bulletin 23(2), pp. 213-225, https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf; Thomas Mack (1999), The Standard Error of Chain Ladder Reserve Estimates: Recursive Calculation and Inclusion of a Tail Factor, https://www.casact.org/sites/default/files/database/astin_vol29no2_361.pdf. Parent topic: Mack claims reserving uncertainty, finite conditional development factor moments, process variance and estimation uncertainty. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackScaledResidual

namespace ActuarialValuation

noncomputable def mackVarianceNumerator (actual predicted exposure : ℕ → ℝ) (m : ℕ) : ℝ := ∑ i ∈ Finset.range m, mackScaledResidual (actual i) (predicted i) (exposure i)

end ActuarialValuation


