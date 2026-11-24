-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTorusInvLevi
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StTorusInvLevi
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:56.045505+00:00
-- url     : https://prove2.me/theorems/d3ae7e68-c705-4090-901e-f9b360c23520
-- title:
--   St Torus Inv Levi
-- statement:
--   Definitions and structural lemmas for St Torus Inv Levi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StTorusInvLevi.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
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
namespace GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo
def TorusInvLevi.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (u : ((Σ k, ι k) → ℂ) → ℝ),
    ContDiffOn ℝ 2 u {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      u (fun p => c p.1 * z p) = u z) →
    ∃ C : ℝ, ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ w : (Σ k, ι k) → ℂ,
      |leviForm u z w| ≤
        C * leviForm (fun y => ∑ k, Real.log ((fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩))) z w
def TorusInvLevi.projectiveLineModulusRatio (z : (Σ _ : Unit, Fin 2) → ℂ) : ℝ :=
  ‖z ⟨(), 0⟩‖ ^ 2 / (‖z ⟨(), 0⟩‖ ^ 2 + ‖z ⟨(), 1⟩‖ ^ 2)
end GroundTheory.Heights₂.Heights.Inter


