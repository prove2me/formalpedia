-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StokesObjects
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StokesObjects
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:07.109463+00:00
-- url     : https://prove2.me/theorems/92638497-ad56-4534-b1de-6e5780a1c5e6
-- title:
--   Stokes Objects
-- statement:
--   Definitions and structural lemmas for Stokes Objects, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StokesObjects.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
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
open ReciprocityTheory.ChartRestriction.G.Geo
def IsDegZeroSmooth {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (u : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∧
    ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z
section
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
end
def planeSq (z : (Σ k, PBlk 3 k) → ℂ) : ℝ := ∑ i : Fin 3, ‖z ⟨(), i⟩‖ ^ 2
def planeBump (z : (Σ k, PBlk 3 k) → ℂ) : ℝ :=
  Real.smoothTransition (4 * ‖z ⟨(), 0⟩‖ ^ 2 / planeSq z - 1)
end GroundTheory.Heights₂.Heights


