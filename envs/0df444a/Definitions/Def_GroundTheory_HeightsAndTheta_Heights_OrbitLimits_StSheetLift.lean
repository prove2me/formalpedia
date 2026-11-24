-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSheetLift
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSheetLift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:06.191656+00:00
-- url     : https://prove2.me/theorems/d85728ef-0f69-4c4e-98a5-3505dfbbfedc
-- title:
--   St Sheet Lift
-- statement:
--   Definitions and structural lemmas for St Sheet Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StSheetLift.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsGenericCount
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
open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre IsSheet PBlk)
def SheetLift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ)
    (h : (Fin e → ℂ) → ((k : K) → ι k) → ℂ),
    IsMultiHomogIdeal P →
    (∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ h y' ∧ (∃ z ∈ mcPts P, segre z = h y') ∧ Ψ (h y') = Fin.cons 1 y') →
      ∃ γ, IsSheet P Ψ y (h y) γ
end GroundTheory.Heights₂.Heights


