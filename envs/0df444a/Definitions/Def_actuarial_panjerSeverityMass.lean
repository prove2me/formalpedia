-- Prove2me | Definitions.Def_actuarial_panjerSeverityMass
-- name    : actuarial_panjerSeverityMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T07:16:55.741983+00:00
-- url     : https://prove2.me/theorems/5a361b25-28ea-4974-87c4-20b2c9b7637e
-- title:
--   Finite claim-size severity and convolution: panjerSeverityMass
-- statement:
--   Truncated severity mass includes loss amounts zero through n, so zero claim size can be audited explicitly. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   M_n=\sum_{j=0}^{n}f_j
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def panjerSeverityMass (f : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range (n+1), f j

end ActuarialValuation


