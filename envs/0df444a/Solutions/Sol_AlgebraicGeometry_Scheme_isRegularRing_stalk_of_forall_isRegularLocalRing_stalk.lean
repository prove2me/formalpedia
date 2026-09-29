-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.isRegularRing_stalk_of_forall_isRegularLocalRing_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/965f5bd2-3251-5e4c-b07e-79e93a01252f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_isRegularRing_stalk_of_forall_isRegularLocalRing_stalk

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

theorem solution
    {X : Scheme.{u}} (hX : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) (x : X) :
    IsRegularRing (X.presheaf.stalk x) := by

  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial

  letI algx : Algebra Γ(X, U) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  haveI hlocx : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  haveI : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  rw [isRegularRing_iff]
  intro q hq

  set T := Localization.AtPrime q with hT
  set q' : Ideal Γ(X, U) := q.comap (algebraMap Γ(X, U) (X.presheaf.stalk x)) with hq'
  haveI hq'p : q'.IsPrime := Ideal.comap_isPrime _ q
  have hlocT : IsLocalization.AtPrime T q' :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      ((hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl) (T := T) q

  set y : PrimeSpectrum Γ(X, U) := ⟨q', hq'p⟩ with hy
  have hyU : hU.fromSpec y ∈ U := by
    have : hU.fromSpec y ∈ Set.range hU.fromSpec := ⟨y, rfl⟩
    rwa [hU.range_fromSpec] at this
  have hlocy := hU.isLocalization_stalk' y hyU
  letI algy : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hyU⟩
  haveI : IsRegularLocalRing (X.presheaf.stalk (hU.fromSpec y)) := hX _

  have e : X.presheaf.stalk (hU.fromSpec y) ≃ₐ[Γ(X, U)] T :=
    @IsLocalization.algEquiv Γ(X, U) _ y.asIdeal.primeCompl (X.presheaf.stalk (hU.fromSpec y)) _ algy hlocy T _ _
      hlocT
  exact IsRegularLocalRing.of_ringEquiv e.toRingEquiv

end S_AlgebraicGeometry_Scheme_isRegularRing_stalk_of_forall_isRegularLocalRing_stalk
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_isRegularRing_stalk_of_forall_isRegularLocalRing_stalk (solution)
