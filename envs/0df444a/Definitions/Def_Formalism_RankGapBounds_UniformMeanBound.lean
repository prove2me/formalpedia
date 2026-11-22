-- Prove2me | Definitions.Def_Formalism_RankGapBounds_UniformMeanBound
-- name    : Formalism_RankGapBounds_UniformMeanBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:17.944072+00:00
-- url     : https://prove2.me/theorems/7e330f61-b1a3-428f-be1a-d45efe6d04dc
-- title:
--   Uniform Mean Bound
-- statement:
--   Definitions and structural lemmas for Uniform Mean Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/UniformMeanBound.lean

import Definitions.Def_Formalism_RankGapBounds_MeanBoundSecondForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
namespace Formalism.RankGapBounds.UniformMeanTopLine
open Formalism.RankGapBounds.WeightedMeanData
noncomputable section
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts)
def Lo4 (u0 : U0) (u : W u0) : ℝ :=
  C.cSl1 * D.IO u0 + C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * Real.log (D.T u0 u) + 1
def SlopesNv4 : Prop :=
  ∀ u0 (u : W u0),
    D.muMaxN u0 u ≤ D.muMaxM u0 u + D.Ga u0 + D.Fo u0 - D.Ee u0 u + C.cSl1 * (m : ℝ) * D.B0 ∧
    D.muM u0 u + D.Ga u0 + D.Fo u0 - D.Ee u0 u - Lo4 D C u0 u ≤ D.muN u0 u
def MLo4 : ℝ :=
  C.cSl1 * D.LoP C + C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * (C.cCount * (m : ℝ) * D.L) + 1
def UBar4 : ℝ :=
  C.cSlope * D.nT * D.a * D.La * (2 + (m : ℝ) / D.k) + D.Vvar C + C.cSl1 * (m : ℝ) * D.B0
    + MLo4 D C
def uniformMeanError : ℝ :=
  D.sumA * (C.cCount * (D.L + (m : ℝ) ^ 2 * D.L / D.k) + 2 * D.logGam / ((f : ℝ) * D.k))
    + (C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε))
    + (m : ℝ) * C.cE * D.B0
    + C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)
    + umean (fun u0 => Real.log (Fintype.card (W u0) : ℝ))
    + D.LoP C
    + MLo4 D C
    + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH) * (UBar4 D C + D.b)
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b))
def UniformMeanBound : Prop :=
  Nonempty U0 → D.HidaSetting C → D.DIV C → D.EComp C → D.HComp C → D.Count C → D.Slopes C →
    SlopesNv4 D C → D.Losses C → D.SlopeIneq → D.HHBound C → D.FParams →
    umean D.ASK ≤ umean D.Main + uniformMeanError D C
end
end Formalism.RankGapBounds.UniformMeanTopLine


