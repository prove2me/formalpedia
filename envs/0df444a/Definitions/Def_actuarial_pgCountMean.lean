-- Prove2me | Definitions.Def_actuarial_pgCountMean
-- name    : actuarial_pgCountMean
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T15:47:38.836872+00:00
-- url     : https://prove2.me/theorems/472560db-52a6-45f5-b3f8-23047178564f
-- title:
--   Aggregate moments, solvency and recursive valuation: pgCountMean
-- statement:
--   Frequency first moment. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \text{Frequency first moment.}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 397. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results on Recursive Evaluation of Compound Distributions, https://doi.org/10.1017/S0515036100006802; S. D. Promislow, Fundamentals of Actuarial Mathematics (2015), chapter 21. Parent topic: Finite-support Panjer counting law, severity convolution powers, aggregate distribution by genuine random-sum weights and corrected zero-severity Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/journals/astin-bulletin-journal-of-the-iaa/article/recursive-evaluation-of-a-family-of-compound-distributions/BD6628F3853600A8F79C6A45E92938CB

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def pgCountMean (p : ℕ → ℝ) (m : ℕ) : ℝ := ∑ j ∈ Finset.range (m+1), (j:ℝ)*p j

end ActuarialValuation


