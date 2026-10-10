-- Prove2me | Definitions.Def_actuarial_panjerPoissonZero
-- name    : actuarial_panjerPoissonZero
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T07:24:47.707787+00:00
-- url     : https://prove2.me/theorems/c7ac25fc-565e-479b-afde-e326d795de28
-- title:
--   Compound Poisson Panjer recurrence: panjerPoissonZero
-- statement:
--   With strictly positive individual claim sizes, aggregate loss zero means zero claims and has Poisson mass exp(-lambda). The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   g_0=e^{-\lambda}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def panjerPoissonZero (lambda : ℝ) : ℝ := Real.exp (-lambda)

end ActuarialValuation


