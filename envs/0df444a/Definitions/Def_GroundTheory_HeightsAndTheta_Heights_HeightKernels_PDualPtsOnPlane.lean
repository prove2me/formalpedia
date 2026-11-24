-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOnPlane
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOnPlane
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:23.506029+00:00
-- url     : https://prove2.me/theorems/5d77afc2-c18a-4a80-9c58-eacc264019ab
-- title:
--   PDual Pts On Plane
-- statement:
--   Definitions and structural lemmas for PDual Pts On Plane, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPtsOnPlane.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
namespace DualPointsOnPlane
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T]
theorem smul_mem_dualLattice (α : 𝓞 K) {φ : Fin i → K} (hφ : φ ∈ dualLattice F) :
    (α : K) • φ ∈ dualLattice F := by
  intro x hx
  obtain ⟨a, ha⟩ := hφ x hx
  refine ⟨α * a, ?_⟩
  rw [map_mul, ha, smul_dotProduct, smul_eq_mul]
def mulMat (b : Module.Basis T ℤ (dualLattice F)) (α : 𝓞 K) (s t : T) : ℤ :=
  b.repr ⟨(α : K) • (b s : Fin i → K), smul_mem_dualLattice α (b s).2⟩ t
def quad (b : Module.Basis T ℤ (dualLattice F)) (α : 𝓞 K) (s r : T) : MRing (dualBlocks T) :=
  X ⟨(), s⟩ * ∑ t, C (mulMat b α r t) * X ⟨(), t⟩ - (∑ t, C (mulMat b α s t) * X ⟨(), t⟩) * X ⟨(), r⟩
end DualPointsOnPlane
end
end GroundTheory.Heights₂.Heights


