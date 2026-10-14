-- Prove2me | Definitions.Def_actuarial_c_expectedLoss
-- name    : actuarial_c_expectedLoss
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:39:51.029274+00:00
-- url     : https://prove2.me/theorems/4787f9ad-d477-4857-b101-8eee8300a069
-- title:
--   Statewise expected value of insurer loss
-- statement:
--   Statewise expected value of insurer loss.
--
--   Mathematical relation:
--
--   $$
--   \mathbb E[L]=\sum_{k=0}^{h}p_kL(k)
--   $$
--
--   This is a separate actuarial cashflow definition, with units of money or present-value factors as determined by its parameters. Timing and endpoint conventions follow the event-level policy-year model.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, net premium ratio and premium stream, printed p. 63. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_premiumPath
import Definitions.Def_actuarial_c_lossPath

namespace ActuarialAssurances

noncomputable def expectedLoss (h n : ℕ) (v premium : ℝ) (b p : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range (h+1), p k*lossPath h n v premium b k
end ActuarialAssurances


