-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartAbsIntegrable
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartAbsIntegrable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:30.228881+00:00
-- url     : https://prove2.me/theorems/74977999-a133-4415-806d-e6fca8232551
-- title:
--   St Segre Chart Abs Integrable
-- statement:
--   Definitions and structural lemmas for St Segre Chart Abs Integrable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StSegreChartAbsIntegrable.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartProjObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsIntegralSegreChartProj
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
open MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar PBlk oneLine isSmoothHerm_oneLine)
open ComplexSets
def SegreChartAbsIntegrable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsDegZeroSmooth g →
      ∀ J ∈ segreChartComponents P σ i, ∀ A : Matrix (Fin e) (Fin m) ℂ, IsFiniteProjection J A →
        Integrable (chartAbsDens J A (chartWeight σ i g) (chartPot σ i L))
end GroundTheory.Heights₂.Heights


