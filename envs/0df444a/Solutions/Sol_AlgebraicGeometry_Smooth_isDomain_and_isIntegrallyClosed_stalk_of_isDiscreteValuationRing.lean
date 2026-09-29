-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/5d2c8be9-c873-539e-96cc-6f6b44375192

import Mathlib
import Theorems.Thm_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] (x : T) :
    IsDomain (T.presheaf.stalk x) ∧ IsIntegrallyClosed (T.presheaf.stalk x) := by
  classical
  obtain ⟨U, hU, V, hV, hxV, hle, -⟩ := Smooth.exists_isStandardSmooth (f := t) x
  have hle' : V ≤ t ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) := le_top
  have hQ : (t.appLE ⊤ V hle').hom.Smooth :=
    HasRingHomProperty.appLE @Smooth t inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ hle'
  let e : R ≃+* Γ(Spec (CommRingCat.of R), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  let ψ : R →+* Γ(T, V) := (t.appLE ⊤ V hle').hom.comp e.toRingHom
  have hψ : ψ.Smooth := RingHom.Smooth.respectsIso.2 _ e hQ
  letI : Algebra R Γ(T, V) := ψ.toAlgebra
  haveI : Algebra.Smooth R Γ(T, V) := RingHom.smooth_algebraMap.mp hψ
  letI : Algebra Γ(T, V) (T.presheaf.stalk x) := (T.presheaf.germ V x hxV).hom.toAlgebra
  haveI := hV.isLocalization_stalk ⟨x, hxV⟩
  exact Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime R Γ(T, V)
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal (T.presheaf.stalk x)

end S_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing (solution)
