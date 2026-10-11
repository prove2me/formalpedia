-- Prove2me | Definitions.Def_actuarial_pgPanjerFactor
-- name    : actuarial_pgPanjerFactor
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T15:45:55.927679+00:00
-- url     : https://prove2.me/theorems/9ed57fb8-561d-4305-b99a-743cd890f823
-- title:
--   Panjer frequency recursion and zero-size correction: pgPanjerFactor
-- statement:
--   Count recursion multiplier a+b/n for a strictly positive count n. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Count recursion multiplier a+b/n for a strictly positive count} \\ \text{n.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 397. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results on Recursive Evaluation of Compound Distributions, https://doi.org/10.1017/S0515036100006802; S. D. Promislow, Fundamentals of Actuarial Mathematics (2015), chapter 21. Parent topic: Finite-support Panjer counting law, severity convolution powers, aggregate distribution by genuine random-sum weights and corrected zero-severity Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/journals/astin-bulletin-journal-of-the-iaa/article/recursive-evaluation-of-a-family-of-compound-distributions/BD6628F3853600A8F79C6A45E92938CB

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def pgPanjerFactor (a b : ℝ) (n : ℕ) : ℝ := a+b/(n:ℝ)

end ActuarialValuation


