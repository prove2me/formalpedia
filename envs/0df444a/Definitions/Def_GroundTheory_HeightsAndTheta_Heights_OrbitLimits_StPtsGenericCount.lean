-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsGenericCount
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsGenericCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:01.14295+00:00
-- url     : https://prove2.me/theorems/0140f300-2c5e-4733-a014-3e43d56b48ef
-- title:
--   St Pts Generic Count
-- statement:
--   Definitions and structural lemmas for St Pts Generic Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StPtsGenericCount.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSheetSimpleNull
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
open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre fibre IsSheet PBlk)
def PtsGenericCount.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
      ∃ d : ℕ, (∀ y, (fibre P Ψ y).encard ≤ d) ∧
        volume {y : Fin e → ℂ | ¬ ((fibre P Ψ y).encard = d ∧
          ∀ w ∈ fibre P Ψ y, ∃ γ, IsSheet P Ψ y w γ)} = 0
end GroundTheory.Heights₂.Heights


