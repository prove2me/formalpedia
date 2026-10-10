-- Prove2me | Definitions.Def_actuarial_panjerSeverityMean
-- name    : actuarial_panjerSeverityMean
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T07:17:03.513013+00:00
-- url     : https://prove2.me/theorems/84b6264f-0780-411d-b55f-4dc25a62e3cb
-- title:
--   Finite claim-size severity and convolution: panjerSeverityMean
-- statement:
--   Truncated mean severity is finite even when tail behaviour is not assumed. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \mu_n=\sum_{j=0}^{n}jf_j
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def panjerSeverityMean (f : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range (n+1), (j : ℝ) * f j

end ActuarialValuation


