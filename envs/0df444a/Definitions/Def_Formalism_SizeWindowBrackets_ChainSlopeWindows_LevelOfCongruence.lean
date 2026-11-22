-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
-- name    : Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:40.23814+00:00
-- url     : https://prove2.me/theorems/60fbd01d-4510-4590-92c4-b75966f4b95e
-- title:
--   Level Of Congruence
-- statement:
--   Definitions and structural lemmas for Level Of Congruence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean

import Definitions.Def_Formalism_SizeWindowBrackets_QuotientSlopeBoundsWith
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_UniformMeanTopLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
namespace Formalism.LFunctionChainParameters.WeightedSlopeBounds
open Formalism.RankGapBounds.WeightedMeanData
noncomputable section
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)
def Lam5 (u0 : U0) : ℝ :=
  (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π)) + (m : ℝ) * D.lg
    - C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k)
def K5v5 (u0 : U0) : ℝ :=
  C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k) + (m : ℝ) * (D.sumA * D.lg + C.cE * D.B0)
    + D.SDiv - D.sumA * Lam5 D C u0 + D.EDiv C
def K0v5 : ℝ :=
  D.sumA * (C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k))
    + D.EDiv C + (m : ℝ) * C.cE * D.B0 + C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)
def K7v5 : ℝ :=
  C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * (C.cCount * (m : ℝ) * D.L) + C.cSl1 * Xpp + 1
end
def C1 : Consts := ⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 1⟩
end Formalism.LFunctionChainParameters.WeightedSlopeBounds


