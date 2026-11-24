-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSheetOnlyNull
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSheetOnlyNull
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:08.398812+00:00
-- url     : https://prove2.me/theorems/5f8c2501-df96-4f63-9a2e-81a5745b65a7
-- title:
--   St Pts Sheet Only Null
-- statement:
--   Definitions and structural lemmas for St Pts Sheet Only Null, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StPtsSheetOnlyNull.lean

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
open MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre fibre IsSheet PBlk)
def PtsSheetOnlyNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → IsGoodProj P Ψ' →
      volume {y : Fin e → ℂ | ∃ w ∈ fibre P Ψ y, IsSimpleSheetPt P Ψ w ∧
        ¬ IsSimpleSheetPt P Ψ' ((Ψ' w 0)⁻¹ • w)} = 0
end GroundTheory.Heights₂.Heights


