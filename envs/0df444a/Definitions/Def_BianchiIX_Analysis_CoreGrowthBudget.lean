-- Prove2me | Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
-- name    : BianchiIX_Analysis_CoreGrowthBudget
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-05T00:31:06.630204+00:00
-- url     : https://prove2.me/theorems/85e6014a-c05d-4002-a485-95e90b9498e4
-- title:
--   An angular growth primitive and a uniform variation bound
-- statement:
--   For real $k,z$, define
--   $$\Gamma_k(z)=2\arctan(\sinh z)+\frac{24}{10000k}z,
--   \qquad C_* = \exp\left(2\pi+\frac{48}{10000}\right).$$
--   Division at zero has its total real-field meaning.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CoreGrowthBudget.lean

import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

namespace BianchiIX

/-- A primitive of the upper bound for the signed row sums. -/
def coreGrowthPrimitive (k z : ℝ) : ℝ :=
  2 * Real.arctan (Real.sinh z) + 24 * ((1 / 10000) / k) * z

def coreVariationBound : ℝ := Real.exp (2 * Real.pi + 48 / 10000)









end BianchiIX


