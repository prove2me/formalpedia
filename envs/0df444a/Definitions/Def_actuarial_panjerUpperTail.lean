-- Prove2me | Definitions.Def_actuarial_panjerUpperTail
-- name    : actuarial_panjerUpperTail
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T07:25:28.090416+00:00
-- url     : https://prove2.me/theorems/c6fa575e-fd2d-4146-a358-a9a3562fa9d2
-- title:
--   Finite aggregate loss reserve and stop-loss valuation: panjerUpperTail
-- statement:
--   The tail mass beyond the threshold is the complement of the finite cumulative aggregate probability. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   T_n=1-G_n
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerAggregateCDF

namespace ActuarialValuation

noncomputable def panjerUpperTail (g : ℕ → ℝ) (n : ℕ) : ℝ := 1 - panjerAggregateCDF g n

end ActuarialValuation


