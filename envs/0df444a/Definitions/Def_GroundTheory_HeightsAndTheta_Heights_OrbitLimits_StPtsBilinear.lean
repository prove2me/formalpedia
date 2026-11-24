-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsBilinear
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsBilinear
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:23.078047+00:00
-- url     : https://prove2.me/theorems/19cb5850-0852-4d18-9abd-2463abc7e2c1
-- title:
--   St Pts Bilinear
-- statement:
--   Definitions and structural lemmas for St Pts Bilinear, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StPtsBilinear.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StokesObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isSmoothHerm_oneLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot PBlk oneLine
  isSmoothHerm_oneLine)
def PtsBilinear.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (T : Type) [Fintype T] (u : T → ((Σ k, ι k) → ℂ) → ℝ)
    (v : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → (∀ t, IsDegZeroSmooth (u t)) →
    IsDegZeroSmooth v →
    ptsIntegral P (Fin.cons v (pot L)) (fun z => ∑ t, u t z) =
        ∑ t, ptsIntegral P (Fin.cons v (pot L)) (u t) ∧
      ptsIntegral P (Fin.cons (fun z => ∑ t, u t z) (pot L)) v =
        ∑ t, ptsIntegral P (Fin.cons (u t) (pot L)) v
end GroundTheory.Heights₂.Heights


