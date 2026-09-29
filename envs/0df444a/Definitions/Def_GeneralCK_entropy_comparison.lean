-- Prove2me | Definitions.Def_GeneralCK_entropy_comparison
-- name    : GeneralCK_entropy_comparison
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T22:20:40.301646+00:00
-- url     : https://prove2.me/theorems/7c79b71a-ad41-4c19-a0f6-df250248bdc7
-- title:
--   The regularized crossover trajectory
-- statement:
--   For real regularization parameter $\varepsilon$ and time $t$, define $$q_\varepsilon(t)=\frac{1-e^{-2t}(1-2\varepsilon)}2.$$ This is the explicit channel trajectory whose binary entropy supplies the comparison curve for entropy production.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/EntropyComparison.lean#L56-L58

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators
namespace GeneralCK.Comparison
open Set





/-- The Bernoulli parameter under the continuous-time binary noise flow. -/
noncomputable def noiseParameter (eps t : ℝ) : ℝ :=
  (1 - Real.exp (-2 * t) * (1 - 2 * eps)) / 2















end GeneralCK.Comparison


