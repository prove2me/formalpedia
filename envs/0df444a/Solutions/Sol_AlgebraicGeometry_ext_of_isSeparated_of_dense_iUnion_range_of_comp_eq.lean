-- Prove2me | solution 1 for AlgebraicGeometry.ext_of_isSeparated_of_dense_iUnion_range_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/da811a71-41b1-5ab6-a79d-466a7e6dfcc2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ext_of_isSeparated_of_dense_iUnion_range_of_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y Z : Scheme.{u}} (f g : X ⟶ Y) (s : Y ⟶ Z) [IsSeparated s] (hs : f ≫ s = g ≫ s) [IsReduced X]
    {ι : Type u} (T : ι → Scheme.{u}) (z : ∀ i, T i ⟶ X) (hz : ∀ i, z i ≫ f = z i ≫ g)
    (hdense : Dense (⋃ i, Set.range (z i).base)) :
    f = g := by
  classical

  let c : (∐ T) ⟶ X := Sigma.desc z
  haveI : IsDominant c := by
    refine ⟨?_⟩
    apply Dense.mono ?_ hdense
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_range] at hx
    obtain ⟨i, t, rfl⟩ := hx
    refine ⟨(Sigma.ι T i).base t, ?_⟩
    show (Sigma.ι T i ≫ c).base t = (z i).base t
    rw [Sigma.ι_desc]
  refine ext_of_isDominant_of_isSeparated s hs c ?_
  apply Sigma.hom_ext
  intro i
  rw [Sigma.ι_desc_assoc, Sigma.ι_desc_assoc, hz]

end S_AlgebraicGeometry_ext_of_isSeparated_of_dense_iUnion_range_of_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_ext_of_isSeparated_of_dense_iUnion_range_of_comp_eq (solution)
