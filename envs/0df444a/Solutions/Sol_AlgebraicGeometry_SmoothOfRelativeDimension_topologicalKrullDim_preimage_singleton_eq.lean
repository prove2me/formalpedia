-- Prove2me | solution 1 for AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_preimage_singleton_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f88a4bb8-db4d-51c1-b640-5af29c23c8f7

import Mathlib
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_preimage_singleton_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) [SmoothOfRelativeDimension n f]
    (y : ↥Y) (hy : (f.base ⁻¹' {y}).Nonempty) :
    topologicalKrullDim ↥(f.base ⁻¹' {y}) = n := by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := n)
  haveI : SmoothOfRelativeDimension n (f.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) f (Y.fromSpecResidueField y) inferInstance
  have hne : Nonempty ↥(f.fiber y) := by
    obtain ⟨x, hx⟩ := hy
    exact ⟨(f.fiberHomeo y).symm ⟨x, hx⟩⟩
  have h1 : (n : WithBot ℕ∞) ≤ topologicalKrullDim ↥(f.fiber y) :=
    AlgebraicGeometry.SmoothOfRelativeDimension.le_topologicalKrullDim
      (K := ↑(Y.residueField y)) (f.fiberToSpecResidueField y) n
  have h2 : topologicalKrullDim ↥(f.fiber y) ≤ n :=
    AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le
      (K := ↑(Y.residueField y)) (f.fiberToSpecResidueField y) n
  have h3 : topologicalKrullDim ↥(f.fiber y) = topologicalKrullDim ↥(f.base ⁻¹' {y}) :=
    IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo y).isHomeomorph
  rw [← h3]
  exact le_antisymm h2 h1

end S_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_preimage_singleton_eq
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_preimage_singleton_eq (solution)
