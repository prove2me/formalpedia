-- Prove2me | Definitions.Def_actuarial_panjerRecursionStep
-- name    : actuarial_panjerRecursionStep
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T07:24:05.86593+00:00
-- url     : https://prove2.me/theorems/c04b9b1a-1888-4079-8146-1ba6d58a6329
-- title:
--   Compound Poisson Panjer recurrence: panjerRecursionStep
-- statement:
--   The one-step compound Poisson Panjer operator assumes strictly positive claim size support, with f(0)=0. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   g_{k+1}=\frac{\lambda}{k+1}\sum_{j=1}^{k+1}jf_jg_{k+1-j}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerWeightedSeverity

namespace ActuarialValuation

noncomputable def panjerRecursionStep (lambda : ℝ) (f g : ℕ → ℝ) (k : ℕ) : ℝ := lambda / ((k+1 : ℕ) : ℝ) * ∑ j ∈ Finset.range (k+1), panjerWeightedSeverity f (j+1) * g (k-j)

end ActuarialValuation


