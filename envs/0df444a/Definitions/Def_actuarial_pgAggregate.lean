-- Prove2me | Definitions.Def_actuarial_pgAggregate
-- name    : actuarial_pgAggregate
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T15:45:27.177996+00:00
-- url     : https://prove2.me/theorems/b885d8e3-9eca-4227-a606-86856733d340
-- title:
--   Discrete severity powers and genuinely compounded frequency: pgAggregate
-- statement:
--   Actual aggregate mass g_k computed from a finite claim-count distribution supported at most m. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Actual aggregate mass g\_k computed from a finite claim-count} \\ \text{distribution supported at most m.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 397. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results on Recursive Evaluation of Compound Distributions, https://doi.org/10.1017/S0515036100006802; S. D. Promislow, Fundamentals of Actuarial Mathematics (2015), chapter 21. Parent topic: Finite-support Panjer counting law, severity convolution powers, aggregate distribution by genuine random-sum weights and corrected zero-severity Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/journals/astin-bulletin-journal-of-the-iaa/article/recursive-evaluation-of-a-family-of-compound-distributions/BD6628F3853600A8F79C6A45E92938CB

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgFold

namespace ActuarialValuation

noncomputable def pgAggregate (p f : ℕ → ℝ) (m k : ℕ) : ℝ := ∑ j ∈ Finset.range (m+1), p j * pgFold f j k

end ActuarialValuation


