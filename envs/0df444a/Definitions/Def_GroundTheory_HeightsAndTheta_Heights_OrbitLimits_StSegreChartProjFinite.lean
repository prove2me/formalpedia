-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartProjFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartProjFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:39.770805+00:00
-- url     : https://prove2.me/theorems/51d2e4ed-f4e3-401b-a62a-04d8aa650cf3
-- title:
--   St Segre Chart Proj Finite
-- statement:
--   Definitions and structural lemmas for St Segre Chart Proj Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StSegreChartProjFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartProjObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsIntegralSegreChartProj
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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj PBlk)
open ComplexSets
def SegreChartProjFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ w, Ψ w 0 = w i) →
      ∀ J ∈ segreChartComponents P σ i, IsFiniteProjection J (chartProjMatrix σ Ψ)
end GroundTheory.Heights₂.Heights


