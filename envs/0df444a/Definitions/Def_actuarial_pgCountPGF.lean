-- Prove2me | Definitions.Def_actuarial_pgCountPGF
-- name    : actuarial_pgCountPGF
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T15:45:33.922708+00:00
-- url     : https://prove2.me/theorems/8e57497f-1ee5-40e2-8bb8-175f7d6a3ad7
-- title:
--   Discrete severity powers and genuinely compounded frequency: pgCountPGF
-- statement:
--   Generating polynomial of finite claim count N including N=0. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \text{Generating polynomial of finite claim count N including N=0.}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 397. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results on Recursive Evaluation of Compound Distributions, https://doi.org/10.1017/S0515036100006802; S. D. Promislow, Fundamentals of Actuarial Mathematics (2015), chapter 21. Parent topic: Finite-support Panjer counting law, severity convolution powers, aggregate distribution by genuine random-sum weights and corrected zero-severity Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/journals/astin-bulletin-journal-of-the-iaa/article/recursive-evaluation-of-a-family-of-compound-distributions/BD6628F3853600A8F79C6A45E92938CB

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def pgCountPGF (p : ℕ → ℝ) (m : ℕ) (z : ℝ) : ℝ := ∑ j ∈ Finset.range (m+1), p j*z^j

end ActuarialValuation


