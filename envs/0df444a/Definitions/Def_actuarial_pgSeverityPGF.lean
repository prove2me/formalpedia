-- Prove2me | Definitions.Def_actuarial_pgSeverityPGF
-- name    : actuarial_pgSeverityPGF
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T15:45:44.121467+00:00
-- url     : https://prove2.me/theorems/9d077f2b-1873-488a-8733-2a22096aeacb
-- title:
--   Discrete severity powers and genuinely compounded frequency: pgSeverityPGF
-- statement:
--   Finite-horizon severity probability generating polynomial. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \text{Finite-horizon severity probability generating polynomial.}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 397. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results on Recursive Evaluation of Compound Distributions, https://doi.org/10.1017/S0515036100006802; S. D. Promislow, Fundamentals of Actuarial Mathematics (2015), chapter 21. Parent topic: Finite-support Panjer counting law, severity convolution powers, aggregate distribution by genuine random-sum weights and corrected zero-severity Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/journals/astin-bulletin-journal-of-the-iaa/article/recursive-evaluation-of-a-family-of-compound-distributions/BD6628F3853600A8F79C6A45E92938CB

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def pgSeverityPGF (f : ℕ → ℝ) (m : ℕ) (z : ℝ) : ℝ := ∑ j ∈ Finset.range (m+1), f j*z^j

end ActuarialValuation


