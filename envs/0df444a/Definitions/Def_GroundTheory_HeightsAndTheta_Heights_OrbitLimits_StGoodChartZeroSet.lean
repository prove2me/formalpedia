-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartZeroSet
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartZeroSet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:12.99184+00:00
-- url     : https://prove2.me/theorems/08caea3e-ab70-46bd-80cc-e609b85e9c86
-- title:
--   St Good Chart Zero Set
-- statement:
--   Definitions and structural lemmas for St Good Chart Zero Set, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StGoodChartZeroSet.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartZeroSet
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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal PBlk)
open ComplexSets
def GoodChartZeroSet.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsMultiHomogIdeal P → zeroSet (projChartIdeal P σ Ψ) = projChartSet P σ Ψ
end GroundTheory.Heights₂.Heights


