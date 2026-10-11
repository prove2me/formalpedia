-- Prove2me | Definitions.Def_actuarial_pgConvolve
-- name    : actuarial_pgConvolve
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T15:45:00.853056+00:00
-- url     : https://prove2.me/theorems/70b8a08d-713b-4fd9-b27d-0a4960069b66
-- title:
--   Discrete severity powers and genuinely compounded frequency: pgConvolve
-- statement:
--   Convolution of two independent nonnegative-integer claim sizes. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \text{Convolution of two independent nonnegative-integer claim sizes.}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 397. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results on Recursive Evaluation of Compound Distributions, https://doi.org/10.1017/S0515036100006802; S. D. Promislow, Fundamentals of Actuarial Mathematics (2015), chapter 21. Parent topic: Finite-support Panjer counting law, severity convolution powers, aggregate distribution by genuine random-sum weights and corrected zero-severity Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/journals/astin-bulletin-journal-of-the-iaa/article/recursive-evaluation-of-a-family-of-compound-distributions/BD6628F3853600A8F79C6A45E92938CB

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def pgConvolve (f g : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ Finset.range (k+1), f j*g (k-j)

end ActuarialValuation


