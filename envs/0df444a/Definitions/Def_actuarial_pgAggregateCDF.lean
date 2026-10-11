-- Prove2me | Definitions.Def_actuarial_pgAggregateCDF
-- name    : actuarial_pgAggregateCDF
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T15:46:49.910417+00:00
-- url     : https://prove2.me/theorems/3a17f27a-1c2d-4cb8-993a-0911e7e7174f
-- title:
--   Aggregate moments, solvency and recursive valuation: pgAggregateCDF
-- statement:
--   Aggregate payout cumulative probability for severities no greater than k. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Aggregate payout cumulative probability for severities no} \\ \text{greater than k.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 397. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results on Recursive Evaluation of Compound Distributions, https://doi.org/10.1017/S0515036100006802; S. D. Promislow, Fundamentals of Actuarial Mathematics (2015), chapter 21. Parent topic: Finite-support Panjer counting law, severity convolution powers, aggregate distribution by genuine random-sum weights and corrected zero-severity Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/journals/astin-bulletin-journal-of-the-iaa/article/recursive-evaluation-of-a-family-of-compound-distributions/BD6628F3853600A8F79C6A45E92938CB

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgAggregate

namespace ActuarialValuation

noncomputable def pgAggregateCDF (p f : ℕ → ℝ) (m k : ℕ) : ℝ := ∑ j ∈ Finset.range (k+1), pgAggregate p f m j

end ActuarialValuation


