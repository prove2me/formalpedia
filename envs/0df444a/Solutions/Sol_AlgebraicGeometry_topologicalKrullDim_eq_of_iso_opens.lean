-- Prove2me | solution 1 for AlgebraicGeometry.topologicalKrullDim_eq_of_iso_opens
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6b60835d-f78a-5934-a06f-e2d17e3de154

import Mathlib
import Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_topologicalKrullDim_eq_of_iso_opens

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem solution
    {k : Type u} [Field k] {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fY] [IsIntegral X] [IsIntegral Y]
    (U : X.Opens) (U' : Y.Opens) (hU : (U : Set X).Nonempty) (e : (U : Scheme.{u}) ≅ (U' : Scheme.{u})) :
    topologicalKrullDim ↥X = topologicalKrullDim ↥Y := by

  obtain ⟨x, hx⟩ := hU
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    (U : Scheme.{u}).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (⟨x, hx⟩ : ↥U))
      isOpen_univ

  have hVX : IsAffineOpen (U.ι ''ᵁ V) := hV.image_of_isOpenImmersion U.ι
  have hVU' : IsAffineOpen (e.hom ''ᵁ V) := hV.image_of_isOpenImmersion e.hom
  have hVY : IsAffineOpen (U'.ι ''ᵁ (e.hom ''ᵁ V)) := hVU'.image_of_isOpenImmersion U'.ι
  have hneX : ((U.ι ''ᵁ V : X.Opens) : Set X).Nonempty := ⟨_, ⟨_, hxV, rfl⟩⟩
  have hneY : ((U'.ι ''ᵁ (e.hom ''ᵁ V) : Y.Opens) : Set Y).Nonempty :=
    ⟨_, ⟨e.hom ⟨x, hx⟩, ⟨_, hxV, rfl⟩, rfl⟩⟩

  let ε : Γ(X, U.ι ''ᵁ V) ≅ Γ(Y, U'.ι ''ᵁ (e.hom ''ᵁ V)) :=
    U.ι.appIso V ≪≫ (e.hom.appIso V).symm ≪≫ (U'.ι.appIso _).symm
  rw [AlgebraicGeometry.topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral fX hVX hneX,
    AlgebraicGeometry.topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral fY hVY hneY]
  exact ringKrullDim_eq_of_ringEquiv ε.commRingCatIsoToRingEquiv

end S_AlgebraicGeometry_topologicalKrullDim_eq_of_iso_opens
end P2MW
export P2MW.S_AlgebraicGeometry_topologicalKrullDim_eq_of_iso_opens (solution)
