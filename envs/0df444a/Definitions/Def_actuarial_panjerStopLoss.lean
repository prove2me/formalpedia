-- Prove2me | Definitions.Def_actuarial_panjerStopLoss
-- name    : actuarial_panjerStopLoss
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T07:25:51.558006+00:00
-- url     : https://prove2.me/theorems/62a303a3-bfda-4405-88ca-5ff679ffe769
-- title:
--   Finite aggregate loss reserve and stop-loss valuation: panjerStopLoss
-- statement:
--   A finite aggregate stop-loss expected ceded payment includes only losses through the truncation horizon. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   SL_n(d)=\sum_{k=0}^{n}(k-d)_+g_k
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def panjerStopLoss (g : ℕ → ℝ) (n : ℕ) (d : ℝ) : ℝ := ∑ k ∈ Finset.range (n+1), max ((k : ℝ) - d) 0 * g k

end ActuarialValuation


