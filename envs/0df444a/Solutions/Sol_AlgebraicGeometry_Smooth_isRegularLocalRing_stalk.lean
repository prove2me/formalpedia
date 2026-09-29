-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.isRegularLocalRing_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/d1dd54cf-b908-54d8-a8e7-67ec1d32ee07

import Mathlib
import Theorems.Thm_isRegularLocalRing_localization_atPrime_of_isStandardSmooth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry IsLocalRing

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
    [Smooth f] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  classical
  obtain ⟨U, hU, V, hV, hxV, hle, hstd⟩ :=
    Smooth.exists_isStandardSmooth (f := f) x
  have hfxU : f.base x ∈ U := hle hxV
  obtain rfl : U = ⊤ := top_le_iff.mp fun y _ => by
    rw [Subsingleton.elim y (f.base x)]; exact hfxU
  let e : k ≃+* Γ(Spec (CommRingCat.of k), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  let ψ : k →+* Γ(X, V) := (f.appLE ⊤ V hle).hom.comp e.toRingHom
  have hψ : ψ.IsStandardSmooth :=
    RingHom.isStandardSmooth_respectsIso.2 _ e hstd
  letI : Algebra k Γ(X, V) := ψ.toAlgebra
  haveI : Algebra.IsStandardSmooth k Γ(X, V) :=
    (RingHom.isStandardSmooth_algebraMap).mp hψ
  haveI hreg : IsRegularLocalRing (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal) :=
    isRegularLocalRing_localization_atPrime_of_isStandardSmooth k Γ(X, V)
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  letI : Algebra Γ(X, V) (X.presheaf.stalk x) := (X.presheaf.germ V x hxV).hom.toAlgebra
  haveI := hV.isLocalization_stalk ⟨x, hxV⟩
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
      (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal) (X.presheaf.stalk x)).toRingEquiv

end S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk (solution)
