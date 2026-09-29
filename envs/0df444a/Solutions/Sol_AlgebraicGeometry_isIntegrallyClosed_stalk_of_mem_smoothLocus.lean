-- Prove2me | solution 1 for AlgebraicGeometry.isIntegrallyClosed_stalk_of_mem_smoothLocus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e0b7f597-6002-5b7b-99ae-7f66a8503047

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIntegrallyClosed_stalk_of_mem_smoothLocus

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation f]
    (y : X) (hy : y ∈ f.smoothLocus) : IsIntegrallyClosed (X.presheaf.stalk y) := by
  set U : X.Opens := f.smoothLocus with hU
  let g : (U : Scheme.{0}) ⟶ Spec (CommRingCat.of R) := U.ι ≫ f
  haveI hlfp : LocallyOfFinitePresentation g := MorphismProperty.comp_mem _ U.ι f inferInstance inferInstance
  have hsm : g.smoothLocus = ⊤ := by
    show (U.ι ≫ f).smoothLocus = ⊤
    rw [← Scheme.Hom.preimage_smoothLocus_eq U.ι f]
    exact Scheme.Opens.ι_preimage_self U
  haveI : Smooth g := Scheme.Hom.smoothLocus_eq_top_iff.mp hsm
  let eΓ : R ≃+* Γ(Spec (CommRingCat.of R), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  haveI : IsDomain Γ(Spec (CommRingCat.of R), ⊤) := eΓ.symm.injective.isDomain eΓ.symm.toRingHom
  haveI : IsIntegrallyClosed Γ(Spec (CommRingCat.of R), ⊤) := IsIntegrallyClosed.of_equiv eΓ
  have hU' : IsIntegrallyClosed ((U : Scheme.{0}).presheaf.stalk (⟨y, hy⟩ : U)) :=
    (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk g (⟨y, hy⟩ : U)).2
  haveI : IsIso (U.ι.stalkMap ⟨y, hy⟩) := inferInstance
  let ε : X.presheaf.stalk y ≃+* (U : Scheme.{0}).presheaf.stalk (⟨y, hy⟩ : U) :=
    (asIso (U.ι.stalkMap ⟨y, hy⟩)).commRingCatIsoToRingEquiv
  exact IsIntegrallyClosed.of_equiv ε.symm

end S_AlgebraicGeometry_isIntegrallyClosed_stalk_of_mem_smoothLocus
end P2MW
export P2MW.S_AlgebraicGeometry_isIntegrallyClosed_stalk_of_mem_smoothLocus (solution)
