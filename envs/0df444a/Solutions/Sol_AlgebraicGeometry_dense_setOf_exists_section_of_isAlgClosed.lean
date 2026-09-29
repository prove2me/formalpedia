-- Prove2me | solution 1 for AlgebraicGeometry.dense_setOf_exists_section_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/b3a37063-a8ef-5559-8235-44a17ed26f6d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_dense_setOf_exists_section_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] :
    Dense {x : X | ∃ s : Spec (.of k) ⟶ X, s ≫ f = 𝟙 _ ∧ s (IsLocalRing.closedPoint k) = x} := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hsub : closedPoints X ⊆
      {x : X | ∃ s : Spec (.of k) ⟶ X, s ≫ f = 𝟙 _ ∧ s (IsLocalRing.closedPoint k) = x} :=
    fun x hx => ⟨pointOfClosedPoint f x hx, pointOfClosedPoint_comp f x hx,
      pointOfClosedPoint_apply f x hx _⟩
  exact Dense.mono hsub (dense_iff_closure_eq.mpr (closure_closedPoints (X := X)))

end S_AlgebraicGeometry_dense_setOf_exists_section_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicGeometry_dense_setOf_exists_section_of_isAlgClosed (solution)
