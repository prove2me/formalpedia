-- Prove2me | Definitions.Def_actuarial_panjerWeightedSeverity
-- name    : actuarial_panjerWeightedSeverity
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T07:23:50.46623+00:00
-- url     : https://prove2.me/theorems/9ee0eb7d-0cd3-42d3-81bf-8e9effb3549c
-- title:
--   Finite claim-size severity and convolution: panjerWeightedSeverity
-- statement:
--   The size-weighted severity coefficient records the expected contribution of a claim of lattice size k. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   w_k=kf_k
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def panjerWeightedSeverity (f : ℕ → ℝ) (k : ℕ) : ℝ := (k : ℝ) * f k

end ActuarialValuation


