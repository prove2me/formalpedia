-- Prove2me | solution 1 for AlgebraicGeometry.base_genericPoint_eq_genericPoint_of_subset_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/c1c67d2f-e0e5-5cea-82d2-8cc3d880ece1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_base_genericPoint_eq_genericPoint_of_subset_range

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {Z X : Scheme.{u}} [IrreducibleSpace ↥Z] [IsIntegral X] (q : Z ⟶ X) (U : X.Opens)
    (hU : (U : Set ↥X).Nonempty) (hsub : (U : Set ↥X) ⊆ Set.range q.base) :
    q.base (genericPoint ↥Z) = genericPoint ↥X := by
  have h1 : IsGenericPoint (q.base (genericPoint ↥Z)) (closure (q.base '' (⊤ : Set ↥Z))) :=
    (genericPoint_spec ↥Z).image q.continuous
  have hdense : closure (q.base '' (⊤ : Set ↥Z)) = (⊤ : Set ↥X) := by
    apply Set.eq_univ_of_univ_subset
    have hUd : Dense (U : Set ↥X) := U.isOpen.dense hU
    rw [← hUd.closure_eq]
    apply closure_minimal _ isClosed_closure
    refine hsub.trans ?_
    rw [Set.top_eq_univ, Set.image_univ]
    exact subset_closure
  rw [hdense] at h1
  exact h1.eq (genericPoint_spec ↥X)

end S_AlgebraicGeometry_base_genericPoint_eq_genericPoint_of_subset_range
end P2MW
export P2MW.S_AlgebraicGeometry_base_genericPoint_eq_genericPoint_of_subset_range (solution)
