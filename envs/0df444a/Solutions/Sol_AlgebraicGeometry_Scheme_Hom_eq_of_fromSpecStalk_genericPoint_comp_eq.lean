-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.eq_of_fromSpecStalk_genericPoint_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/105e003e-2d86-5261-8595-601e5d79f92e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_eq_of_fromSpecStalk_genericPoint_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem solution
    {U H S : Scheme.{u}} [IsIntegral U] (sU : U ⟶ S) (sH : H ⟶ S) [IsSeparated sH]
    (f g : U ⟶ H) (hf : f ≫ sH = sU) (hg : g ≫ sH = sU)
    (h : U.fromSpecStalk (genericPoint U) ≫ f = U.fromSpecStalk (genericPoint U) ≫ g) :
    f = g := by
  haveI : IsDominant (U.fromSpecStalk (genericPoint U)) := by
    constructor
    have hmem : genericPoint U ∈ Set.range (U.fromSpecStalk (genericPoint U)).base :=
      ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
    have hd : Dense ({genericPoint U} : Set U) := by
      rw [dense_iff_closure_eq]
      exact genericPoint_closure U
    exact hd.mono (Set.singleton_subset_iff.mpr hmem)
  exact ext_of_isDominant_of_isSeparated sH (hf.trans hg.symm) (U.fromSpecStalk (genericPoint U)) h

end S_AlgebraicGeometry_Scheme_Hom_eq_of_fromSpecStalk_genericPoint_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_eq_of_fromSpecStalk_genericPoint_comp_eq (solution)
