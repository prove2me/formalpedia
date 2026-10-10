-- Prove2me | Definitions.Def_actuarial_panjerRecurrenceLaw
-- name    : actuarial_panjerRecurrenceLaw
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T07:24:40.294934+00:00
-- url     : https://prove2.me/theorems/dd68db36-88cc-4b67-9480-1993fccccc52
-- title:
--   Compound Poisson Panjer recurrence: panjerRecurrenceLaw
-- statement:
--   A compound Poisson aggregate coefficient sequence is specified by its zero-loss mass and the full positive-claim-size recurrence. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   g_0=e^{-\lambda},\quad g_{k+1}=\frac{\lambda}{k+1}\sum_{j=1}^{k+1}jf_jg_{k+1-j}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerRecursionStep

namespace ActuarialValuation

noncomputable def panjerRecurrenceLaw (lambda : ℝ) (f g : ℕ → ℝ) : Prop := g 0 = Real.exp (-lambda) ∧ ∀ k : ℕ, g (k+1) = panjerRecursionStep lambda f g k

end ActuarialValuation


