-- Prove2me | solution 1 for AlgebraicGeometry.existsUnique_hom_comp_eq_specMap_and_specMap_comp_eq_of_isProper_of_valuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/de1a6d31-3775-5e4a-857e-795c7f0cc22b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_existsUnique_hom_comp_eq_specMap_and_specMap_comp_eq_of_isProper_of_valuationSubring

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    {K : Type u} [Field K] (A : ValuationSubring K)
    (ρ : R →+* ↥A)
    (x : Spec (CommRingCat.of K) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom ρ)) :
    ∃! s : Spec (CommRingCat.of ↥A) ⟶ X,
      s ≫ f = Spec.map (CommRingCat.ofHom ρ) ∧ Spec.map (CommRingCat.ofHom A.subtype) ≫ s = x := by
  have hval : ValuativeCriterion f := by
    have h := congrFun (congrFun (congrFun AlgebraicGeometry.IsProper.eq_valuativeCriterion X) (Spec (CommRingCat.of R))) f
    have hP : IsProper f := inferInstance
    rw [h] at hP
    exact hP.1.1.1
  have hsq : CommSq x (Spec.map (CommRingCat.ofHom (algebraMap ↥A K))) f (Spec.map (CommRingCat.ofHom ρ)) := ⟨hx⟩
  let S : ValuativeCommSq f :=
    { R := ↥A, K := K, i₁ := x, i₂ := Spec.map (CommRingCat.ofHom ρ), commSq := hsq }
  obtain ⟨huniq⟩ := hval S
  let l := (default : S.commSq.LiftStruct)
  refine ⟨l.l, ⟨l.fac_right, l.fac_left⟩, ?_⟩
  rintro s ⟨hs₁, hs₂⟩
  have : (⟨s, hs₂, hs₁⟩ : S.commSq.LiftStruct) = l := Subsingleton.elim _ _
  exact congrArg CommSq.LiftStruct.l this

#print axioms solution

end S_AlgebraicGeometry_existsUnique_hom_comp_eq_specMap_and_specMap_comp_eq_of_isProper_of_valuationSubring
end P2MW
export P2MW.S_AlgebraicGeometry_existsUnique_hom_comp_eq_specMap_and_specMap_comp_eq_of_isProper_of_valuationSubring (solution)
