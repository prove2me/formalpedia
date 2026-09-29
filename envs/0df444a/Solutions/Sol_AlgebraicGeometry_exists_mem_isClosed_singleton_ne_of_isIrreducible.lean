-- Prove2me | solution 1 for AlgebraicGeometry.exists_mem_isClosed_singleton_ne_of_isIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/9aeb42b0-feda-583a-bf47-061788637eaa

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_mem_isClosed_singleton_ne_of_isIrreducible

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    (k : Type u) [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t]
    (Z : Set X) (hZ : IsClosed Z) (hZ' : IsIrreducible Z)
    (x : X) (hxZ : x ∈ Z) (hx : IsClosed ({x} : Set X)) (hne : Z ≠ {x}) :
    ∃ x' ∈ Z, IsClosed ({x'} : Set X) ∧ x' ≠ x := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace t
  by_contra h
  push Not at h
  apply hne
  have hsub : Z ∩ closedPoints X ⊆ {x} := by
    rintro y ⟨hyZ, hy⟩
    exact h y hyZ (mem_closedPoints_iff.mp hy)
  have h1 : Z ⊆ {x} := by
    rw [← JacobsonSpace.closure_inter_closedPoints hZ]
    exact (closure_mono hsub).trans hx.closure_subset
  exact Set.Subset.antisymm h1 (Set.singleton_subset_iff.mpr hxZ)

end S_AlgebraicGeometry_exists_mem_isClosed_singleton_ne_of_isIrreducible
end P2MW
export P2MW.S_AlgebraicGeometry_exists_mem_isClosed_singleton_ne_of_isIrreducible (solution)
