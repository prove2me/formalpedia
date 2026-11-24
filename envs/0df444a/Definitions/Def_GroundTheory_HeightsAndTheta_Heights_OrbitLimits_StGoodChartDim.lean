-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartDim
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartDim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:28.146702+00:00
-- url     : https://prove2.me/theorems/8a2f277c-ec68-49a9-9f04-05b20fb92aa0
-- title:
--   St Good Chart Dim
-- statement:
--   Definitions and structural lemmas for St Good Chart Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StGoodChartDim.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartModel
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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar PBlk)
def GoodChartDim.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) →
      ∀ J ∈ (projChartIdeal P σ Ψ).minimalPrimes,
        ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ)
end GroundTheory.Heights₂.Heights


