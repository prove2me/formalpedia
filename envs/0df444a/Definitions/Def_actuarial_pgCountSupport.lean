-- Prove2me | Definitions.Def_actuarial_pgCountSupport
-- name    : actuarial_pgCountSupport
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T15:46:33.968687+00:00
-- url     : https://prove2.me/theorems/7dd5c242-3496-445d-bf26-05b3576cc1e2
-- title:
--   Panjer frequency recursion and zero-size correction: pgCountSupport
-- statement:
--   Count distribution is identically zero after its finite upper support m. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Count distribution is identically zero after its finite upper} \\ \text{support m.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 397. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results on Recursive Evaluation of Compound Distributions, https://doi.org/10.1017/S0515036100006802; S. D. Promislow, Fundamentals of Actuarial Mathematics (2015), chapter 21. Parent topic: Finite-support Panjer counting law, severity convolution powers, aggregate distribution by genuine random-sum weights and corrected zero-severity Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/journals/astin-bulletin-journal-of-the-iaa/article/recursive-evaluation-of-a-family-of-compound-distributions/BD6628F3853600A8F79C6A45E92938CB

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

def pgCountSupport (p : ℕ → ℝ) (m : ℕ) : Prop := ∀ n : ℕ, m<n → p n=0

end ActuarialValuation


