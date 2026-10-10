-- Prove2me | Definitions.Def_actuarial_panjerFrequencyPremium
-- name    : actuarial_panjerFrequencyPremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T07:24:55.939876+00:00
-- url     : https://prove2.me/theorems/88e388f5-e55f-43f0-8578-3523e6a30549
-- title:
--   Compound Poisson Panjer recurrence: panjerFrequencyPremium
-- statement:
--   A pure aggregate risk premium is frequency intensity times mean severity under the compound Poisson model. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \Pi=\lambda\mu
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def panjerFrequencyPremium (lambda meanSeverity : ℝ) : ℝ := lambda * meanSeverity

end ActuarialValuation


