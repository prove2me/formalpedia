-- Prove2me | Definitions.Def_actuarial_panjerConvolution
-- name    : actuarial_panjerConvolution
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T07:23:42.300081+00:00
-- url     : https://prove2.me/theorems/99143127-5d7b-4cf7-8b4a-8559fc68e571
-- title:
--   Finite claim-size severity and convolution: panjerConvolution
-- statement:
--   Finite discrete convolution forms a basic aggregate-claims valuation building block. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   (f*g)_k=\sum_{j=0}^{k}f_jg_{k-j}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def panjerConvolution (f g : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ Finset.range (k+1), f j * g (k-j)

end ActuarialValuation


