-- Prove2me | Definitions.Def_Formalism_RankGapBounds_MeanBoundSecondForm
-- name    : Formalism_RankGapBounds_MeanBoundSecondForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:45:56.429062+00:00
-- url     : https://prove2.me/theorems/32ad326d-63bf-4d95-af7e-d325ac07f177
-- title:
--   Mean Bound Second Form
-- statement:
--   Definitions and structural lemmas for Mean Bound Second Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/MeanBoundSecondForm.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
namespace Formalism.RankGapBounds.WeightedMeanData
noncomputable section
def ph (y : ℝ) : ℝ := y * Real.log y - y
def wmean {ι : Type} [Fintype ι] (d X : ι → ℝ) : ℝ := (∑ i, d i * X i) / (∑ i, d i)
def umean {ι : Type} [Fintype ι] (X : ι → ℝ) : ℝ := (∑ i, X i) / (Fintype.card ι : ℝ)
structure Consts where

  cDiv : ℝ

  eDiv : ℝ

  cE : ℝ

  cH : ℝ

  cCount : ℝ

  cSlope : ℝ

  cSl1 : ℝ

  cLoss : ℝ

  eLoss : ℝ

  cHH : ℝ
structure Data (U0 : Type) (W : U0 → Type) (Top : Type) (m f : ℕ) where
  x : ℝ
  ε : ℝ
  a : ℝ
  b : ℝ
  b' : ℝ
  k : ℝ
  L : ℝ
  La : ℝ
  B0 : ℝ
  Nc : ℝ
  gam : ℝ
  LpL : ℝ
  v : ℝ
  lg : ℝ
  logGam : ℝ
  aT : Top → ℝ
  w : U0 → Fin m → Fin f → ℝ
  d : (u0 : U0) → W u0 → ℝ
  T : (u0 : U0) → W u0 → ℝ
  muN : (u0 : U0) → W u0 → ℝ
  muMaxN : (u0 : U0) → W u0 → ℝ
  h : (u0 : U0) → W u0 → ℝ
  muM : (u0 : U0) → W u0 → ℝ
  muMaxM : (u0 : U0) → W u0 → ℝ
  EeJ : (u0 : U0) → W u0 → Fin m → ℝ
  muCC : U0 → ℝ
  muMinCC : U0 → ℝ
  Fo : U0 → ℝ
  Ga : U0 → ℝ
  Ta : U0 → ℝ
  ASK : U0 → ℝ
  IO : U0 → ℝ
  HH : U0 → ℝ
  del : U0 → ℝ
  η : U0 → ℝ
  e : U0 → ℝ
  delBar : ℝ
  etaBar : ℝ
  eBar : ℝ
namespace Data
variable {U0 : Type} [Fintype U0] [Nonempty U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts)
def nT (_ : Data U0 W Top m f) : ℝ := (Fintype.card Top : ℝ)
def sumA : ℝ := ∑ t, D.aT t
def logOm : ℝ := D.gam + Real.log (π / D.v) - D.LpL
def Ee (u0 : U0) (u : W u0) : ℝ := ∑ j, D.EeJ u0 u j
def s (u0 : U0) : ℝ := wmean (D.d u0) (fun u => D.muN u0 u - D.h u0 u)
def uF (u0 : U0) : ℝ :=
  (Finset.univ.sup' Finset.univ_nonempty (fun u : W u0 => D.muMaxN u0 u - D.h u0 u)) - D.s u0
def Tterm (u0 : U0) (u : W u0) : ℝ :=
  (4 * (f : ℝ) / D.T u0 u) *
    (|D.Ga u0| + D.Ta u0 + D.muMaxM u0 u - D.muM u0 u + 2 * (f : ℝ) * Real.log (D.T u0 u))
def Lo (u0 : U0) (u : W u0) : ℝ :=
  C.cSl1 * D.IO u0 + C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * Real.log (D.T u0 u)
    + C.cSl1 * (m : ℝ) * D.B0 + D.Tterm u0 u
def LoP : ℝ := C.cLoss * D.nT * (m : ℝ) * D.b * D.x ^ (C.eLoss * D.ε)
def Main (u0 : U0) : ℝ :=
  ∑ j : Fin m, ∑ t, D.aT t * (Real.log (D.aT t) - 1 - D.gam + D.LpL
    - (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ))
def HidaSetting : Prop :=
  0 < D.x ∧ 0 < D.b ∧ 0 ≤ D.a ∧ 0 ≤ D.b' ∧ 0 < D.k ∧ 0 < D.v ∧ 0 < f ∧
  (∀ t, 0 ≤ D.aT t) ∧ (∀ u0 j ρ, 0 < D.w u0 j ρ) ∧
  (∀ u0 (u : W u0), 0 < D.d u0 u) ∧ (∀ u0 (u : W u0), 0 < D.T u0 u) ∧
  (∀ u0 (u : W u0), D.muN u0 u ≤ D.muMaxN u0 u) ∧
  0 ≤ C.cSl1 ∧ D.delBar < 1 ∧ 0 ≤ D.etaBar ∧ 0 ≤ D.eBar ∧ D.eBar ≤ 1 / 4
def DIV : Prop :=
  ∀ u0 (u : W u0), D.muCC u0 + D.h u0 u - D.Fo u0 ≤
    (∑ t, ((m : ℝ) * (ph (D.aT t) - D.aT t * D.logOm) - D.aT t * Real.log (D.T u0 u)))
      + C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε)
def EComp : Prop :=
  ∀ u0 (u : W u0) (j : Fin m), |D.EeJ u0 u j - D.sumA * D.lg| ≤ C.cE * D.B0
def HComp : Prop :=
  ∀ u0 (u u' : W u0),
    |(D.h u0 u + ∑ t, D.aT t * Real.log (D.T u0 u)) - (D.h u0 u' + ∑ t, D.aT t * Real.log (D.T u0 u'))|
      ≤ C.cH * (D.nT * D.a * D.La + (m : ℝ) * D.B0)
def Count : Prop :=
  ∀ u0 (u : W u0),
    ((∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π)) + (m : ℝ) * D.lg
        - C.cCount * (D.L + (m : ℝ) ^ 2 * D.L / D.k) - 2 * D.logGam / ((f : ℝ) * D.k)
        ≤ Real.log (D.T u0 u)) ∧
    Real.log (D.T u0 u) ≤ C.cCount * (m : ℝ) * D.L ∧
    ∀ u' : W u0, |Real.log (D.T u0 u) - Real.log (D.T u0 u')| ≤ C.cCount * Real.log D.k
def Slopes : Prop :=
  ∀ u0 (u : W u0), -(C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)) ≤ D.muM u0 u ∧
    D.muMaxM u0 u ≤ C.cSlope * D.nT * D.a * D.La
def SlopesN : Prop :=
  ∀ u0 (u : W u0),
    D.muMaxN u0 u ≤ D.muMaxM u0 u + D.Ga u0 + D.Fo u0 - D.Ee u0 u + C.cSl1 * (m : ℝ) * D.B0 ∧
    D.muM u0 u + D.Ga u0 + D.Fo u0 - D.Ee u0 u - D.Lo C u0 u ≤ D.muN u0 u
def Losses : Prop :=
  umean (fun u0 => D.ASK u0 - D.Ga u0) ≤ D.LoP C ∧ umean D.IO ≤ D.LoP C
def SlopeIneq : Prop :=
  ∀ u0, 0 ≤ D.del u0 → D.del u0 < 1 → 0 ≤ D.η u0 → 0 ≤ D.e u0 → D.e u0 ≤ 1 / 4 →
    D.s u0 - D.muMinCC u0 ≤ D.HH u0 → 0 < D.HH u0 →
    D.s u0 - Real.log (Fintype.card (W u0) : ℝ)
      - (1 - D.del u0)⁻¹ * (4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0)
          + (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0) ≤ D.muCC u0
def HHBound : Prop :=
  ∀ u0, D.s u0 - D.muMinCC u0 ≤ D.HH u0 ∧ 0 < D.HH u0 ∧ D.HH u0 ≤ D.x ^ C.cHH * D.b
def FParams : Prop :=
  ∀ u0, 0 ≤ D.del u0 ∧ D.del u0 ≤ D.delBar ∧ 0 ≤ D.η u0 ∧ D.η u0 ≤ D.etaBar ∧
    0 ≤ D.e u0 ∧ D.e u0 ≤ D.eBar
def Vvar : ℝ :=
  2 * (m : ℝ) * C.cE * D.B0 + C.cH * (D.nT * D.a * D.La + (m : ℝ) * D.B0)
    + D.sumA * (C.cCount * Real.log D.k)
def MLo : ℝ :=
  C.cSl1 * D.LoP C + C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * (C.cCount * (m : ℝ) * D.L)
    + C.cSl1 * (m : ℝ) * D.B0 + umean (fun u0 => wmean (D.d u0) (D.Tterm u0))
def UBar : ℝ :=
  C.cSlope * D.nT * D.a * D.La * (2 + (m : ℝ) / D.k) + D.Vvar C + C.cSl1 * (m : ℝ) * D.B0 + D.MLo C
def ErrX : ℝ :=
  D.sumA * (C.cCount * (D.L + (m : ℝ) ^ 2 * D.L / D.k) + 2 * D.logGam / ((f : ℝ) * D.k))
    + (C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε))
    + (m : ℝ) * C.cE * D.B0
    + C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)
    + umean (fun u0 => Real.log (Fintype.card (W u0) : ℝ))
    + D.LoP C
    + D.MLo C
    + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH) * (D.UBar C + D.b)
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b))
def MeanBoundSecondForm : Prop :=
  Nonempty U0 → D.HidaSetting C → D.DIV C → D.EComp C → D.HComp C → D.Count C → D.Slopes C → D.SlopesN C →
    D.Losses C → D.SlopeIneq → D.HHBound C → D.FParams →
    umean D.ASK ≤ umean D.Main + D.ErrX C
def TaBound (cTa Xp Bo : ℝ) : Prop :=
  1 ≤ Xp ∧ 0 ≤ Bo ∧ ∀ u0, D.Ta u0 ≤ cTa * (m : ℝ) * D.nT * D.a * Real.log Xp + Bo
def TaB (cTa Xp Bo : ℝ) : ℝ := cTa * (m : ℝ) * D.nT * D.a * Real.log Xp + Bo
def TtermB (cTa Xp Bo : ℝ) (u0 : U0) (u : W u0) : ℝ :=
  (4 * (f : ℝ) / D.T u0 u) *
    (|D.Ga u0| + D.TaB cTa Xp Bo + D.muMaxM u0 u - D.muM u0 u + 2 * (f : ℝ) * Real.log (D.T u0 u))
def MLoB (cTa Xp Bo : ℝ) : ℝ :=
  C.cSl1 * D.LoP C + C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * (C.cCount * (m : ℝ) * D.L)
    + C.cSl1 * (m : ℝ) * D.B0 + umean (fun u0 => wmean (D.d u0) (D.TtermB cTa Xp Bo u0))
def UBarB (cTa Xp Bo : ℝ) : ℝ :=
  C.cSlope * D.nT * D.a * D.La * (2 + (m : ℝ) / D.k) + D.Vvar C + C.cSl1 * (m : ℝ) * D.B0
    + D.MLoB C cTa Xp Bo
def ErrXB (cTa Xp Bo : ℝ) : ℝ :=
  D.sumA * (C.cCount * (D.L + (m : ℝ) ^ 2 * D.L / D.k) + 2 * D.logGam / ((f : ℝ) * D.k))
    + (C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε))
    + (m : ℝ) * C.cE * D.B0
    + C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)
    + umean (fun u0 => Real.log (Fintype.card (W u0) : ℝ))
    + D.LoP C
    + D.MLoB C cTa Xp Bo
    + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH) * (D.UBarB C cTa Xp Bo + D.b)
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b))
def MeanBoundOfTail (cTa Xp Bo : ℝ) : Prop :=
  Nonempty U0 → D.HidaSetting C → D.DIV C → D.EComp C → D.HComp C → D.Count C → D.Slopes C →
    D.SlopesN C → D.Losses C → D.SlopeIneq → D.HHBound C → D.FParams → D.TaBound cTa Xp Bo →
    umean D.ASK ≤ umean D.Main + D.ErrXB C cTa Xp Bo
end Data
end
end Formalism.RankGapBounds.WeightedMeanData


