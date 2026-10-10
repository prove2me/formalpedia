-- Prove2me | Definitions.Def_actuarial_panjerAggregateMean
-- name    : actuarial_panjerAggregateMean
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T07:25:42.777313+00:00
-- url     : https://prove2.me/theorems/4d76d463-714d-47d7-82fb-1ee0f22e961b
-- title:
--   Finite aggregate loss reserve and stop-loss valuation: panjerAggregateMean
-- statement:
--   A truncated pure claims cost is the finite first moment of the aggregate loss distribution. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   m_n=\sum_{k=0}^{n}kg_k
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def panjerAggregateMean (g : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range (n+1), (k : ℝ) * g k

end ActuarialValuation


