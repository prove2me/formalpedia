-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/9e1c7401-b33e-5d30-9f51-cf8c790ff8ef

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem solution
    {X : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
    (hdim : ∀ x : X, x ≠ genericPoint X → IsClosed ({x} : Set X)) :
    ∀ Z : Set X, IsClosed Z → Z ≠ Set.univ → Z.Finite := by
  intro Z hZ hne
  obtain ⟨S, hSfin, hSclosed, hSirr, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  refine Set.Finite.sUnion hSfin fun t ht => ?_

  obtain ⟨z, hz⟩ := QuasiSober.sober (hSirr t ht) (hSclosed t ht)
  have hzne : z ≠ genericPoint X := by
    rintro rfl
    apply hne
    apply Set.eq_univ_of_univ_subset
    calc Set.univ = closure ({genericPoint X} : Set X) := (genericPoint_closure X).symm
      _ = t := hz.def
      _ ⊆ ⋃₀ S := Set.subset_sUnion_of_mem ht
  have ht1 : t = {z} := by rw [← hz.def, (hdim z hzne).closure_eq]
  rw [ht1]
  exact Set.finite_singleton z

end S_AlgebraicGeometry_Scheme_finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton (solution)
