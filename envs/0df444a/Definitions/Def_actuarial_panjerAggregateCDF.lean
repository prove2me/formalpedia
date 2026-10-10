-- Prove2me | Definitions.Def_actuarial_panjerAggregateCDF
-- name    : actuarial_panjerAggregateCDF
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T07:25:12.026257+00:00
-- url     : https://prove2.me/theorems/2a459015-542c-40d0-a661-4248da067a97
-- title:
--   Finite aggregate loss reserve and stop-loss valuation: panjerAggregateCDF
-- statement:
--   The truncated aggregate claims distribution function accumulates lattice probabilities through n. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   G_n=\sum_{k=0}^ng_k
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def panjerAggregateCDF (g : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range (n+1), g k

end ActuarialValuation


