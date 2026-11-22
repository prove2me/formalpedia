-- Prove2me | Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
-- name    : Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:47:52.079175+00:00
-- url     : https://prove2.me/theorems/1fddac91-2449-4ab6-a3d1-1d66f1b1fdc5
-- title:
--   Weighted Mean Data
-- statement:
--   Definitions and structural lemmas for Weighted Mean Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean

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
namespace Formalism.RankGapBounds.WeightedMeanData
noncomputable section
section Means
variable {ι : Type} [Fintype ι]
end Means
namespace Data
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts)
def abelian₂ (u0 : U0) : ℝ :=
  (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π)) + (m : ℝ) * D.lg
    - C.cCount * (D.L + (m : ℝ) ^ 2 * D.L / D.k) - 2 * D.logGam / ((f : ℝ) * D.k)
def SDiv : ℝ := ∑ t, (m : ℝ) * (ph (D.aT t) - D.aT t * D.logOm)
def EDiv : ℝ :=
  C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε)
def K5 (u0 : U0) : ℝ :=
  C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k) + (m : ℝ) * (D.sumA * D.lg + C.cE * D.B0)
    + D.SDiv - D.sumA * D.abelian₂ C u0 + D.EDiv C
def K3 : ℝ :=
  C.cSlope * D.nT * D.a * D.La * (2 + (m : ℝ) / D.k) + D.Vvar C + C.cSl1 * (m : ℝ) * D.B0
def K7 : ℝ :=
  C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * (C.cCount * (m : ℝ) * D.L)
    + C.cSl1 * (m : ℝ) * D.B0
def K0 : ℝ :=
  D.sumA * (C.cCount * (D.L + (m : ℝ) ^ 2 * D.L / D.k) + 2 * D.logGam / ((f : ℝ) * D.k))
    + D.EDiv C + (m : ℝ) * C.cE * D.B0 + C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)
end Data
end
end Formalism.RankGapBounds.WeightedMeanData


