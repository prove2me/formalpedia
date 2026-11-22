-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_QuotientSlopeBoundsWith
-- name    : Formalism_SizeWindowBrackets_QuotientSlopeBoundsWith
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:00.577173+00:00
-- url     : https://prove2.me/theorems/2fd5e5d6-aaca-43ca-ad41-565c82925431
-- title:
--   Quotient Slope Bounds With
-- statement:
--   Definitions and structural lemmas for Quotient Slope Bounds With, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean

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
namespace Formalism.LFunctionChainParameters.WeightedSlopeBounds
open Formalism.RankGapBounds.WeightedMeanData
noncomputable section
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)
def Lo5 (u0 : U0) (u : W u0) : ℝ :=
  C.cSl1 * D.IO u0 + C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * Real.log (D.T u0 u)
    + C.cSl1 * Xpp + 1
def QuotientSlopeBoundsWith : Prop :=
  ∀ u0 (u : W u0),
    D.muMaxN u0 u ≤ D.muMaxM u0 u + D.Ga u0 + D.Fo u0 - D.Ee u0 u + C.cSl1 * (m : ℝ) * D.B0 ∧
    D.muM u0 u + D.Ga u0 + D.Fo u0 - D.Ee u0 u - Lo5 D C Xpp u0 u ≤ D.muN u0 u
def EComp5 : Prop :=
  ∀ u0 (u : W u0), |D.Ee u0 u - (m : ℝ) * D.sumA * D.lg| ≤ C.cE * (m : ℝ) * D.B0
def Count5 : Prop :=
  ∀ u0 (u : W u0),
    ((∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π)) + (m : ℝ) * D.lg
        - C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k) ≤ Real.log (D.T u0 u)) ∧
    Real.log (D.T u0 u) ≤ C.cCount * (m : ℝ) * D.L ∧
    ∀ u' : W u0, |Real.log (D.T u0 u) - Real.log (D.T u0 u')| ≤ C.cCount * Real.log D.k
def LossBounds : Prop :=
  ∀ u0, D.ASK u0 - D.Ga u0 ≤ D.LoP C ∧ D.IO u0 ≤ D.LoP C
def MLo5 : ℝ :=
  C.cSl1 * D.LoP C + C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * (C.cCount * (m : ℝ) * D.L)
    + C.cSl1 * Xpp + 1
def UBar5 : ℝ :=
  C.cSlope * D.nT * D.a * D.La * (2 + (m : ℝ) / D.k) + D.Vvar C + C.cSl1 * (m : ℝ) * D.B0
    + MLo5 D C Xpp
def ErrX5at (u0 : U0) : ℝ :=
  D.sumA * (C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k))
    + (C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε))
    + (m : ℝ) * C.cE * D.B0
    + C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)
    + Real.log (Fintype.card (W u0) : ℝ)
    + D.LoP C
    + MLo5 D C Xpp
    + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH) * (UBar5 D C Xpp + D.b)
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b))
def errorTermWith : ℝ :=
  D.sumA * (C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k))
    + (C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε))
    + (m : ℝ) * C.cE * D.B0
    + C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)
    + umean (fun u0 => Real.log (Fintype.card (W u0) : ℝ))
    + D.LoP C
    + MLo5 D C Xpp
    + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH) * (UBar5 D C Xpp + D.b)
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b))
def MeanBoundWith : Prop :=
  Nonempty U0 → D.HidaSetting C → D.DIV C → EComp5 D C → D.HComp C → Count5 D C → D.Slopes C →
    QuotientSlopeBoundsWith D C Xpp → LossBounds D C → D.SlopeIneq → D.HHBound C → D.FParams →
    umean D.ASK ≤ umean D.Main + errorTermWith D C Xpp
def PointwiseBoundVariant : Prop :=
  D.HidaSetting C → D.DIV C → EComp5 D C → D.HComp C → Count5 D C → D.Slopes C →
    QuotientSlopeBoundsWith D C Xpp → LossBounds D C → D.SlopeIneq → D.HHBound C → D.FParams →
    ∀ u0, D.ASK u0 ≤ D.Main u0 + ErrX5at D C Xpp u0
def MeanBoundOfLossBounds : Prop :=
  Nonempty U0 → D.HidaSetting C → D.DIV C → EComp5 D C → D.HComp C → Count5 D C → D.Slopes C →
    QuotientSlopeBoundsWith D C Xpp → D.Losses C → D.SlopeIneq → D.HHBound C → D.FParams →
    umean D.ASK ≤ umean D.Main + errorTermWith D C Xpp
end
end Formalism.LFunctionChainParameters.WeightedSlopeBounds


