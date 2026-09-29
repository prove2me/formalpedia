-- Prove2me | solution 1 for AlgebraicGeometry.finite_setOf_pullback_fst_eq_of_isClosed_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/9c704511-f9e6-5017-8bb5-f577bffcdc4b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_finite_setOf_pullback_fst_eq_of_isClosed_singleton

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem solution
    {κ Ω : Type u} [Field κ] [Field Ω] [Algebra κ Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of κ)) [LocallyOfFiniteType f]
    (z : X) (hz : IsClosed ({z} : Set X)) :
    {w : ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap κ Ω)))) |
      (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap κ Ω)))) w = z}.Finite := by
  classical
  set s := Spec.map (CommRingCat.ofHom (algebraMap κ Ω)) with hs

  have hr := Scheme.Pullback.range_snd (X.fromSpecResidueField z) (pullback.fst f s)
  rw [Scheme.range_fromSpecResidueField] at hr
  have hset : {w : ↥(pullback f s) | pullback.fst f s w = z} =
      Set.range (pullback.snd (X.fromSpecResidueField z) (pullback.fst f s)) := by
    rw [hr]; ext w; simp
  rw [hset]

  let φ : CommRingCat.of κ ⟶ X.residueField z := Spec.preimage (X.fromSpecResidueField z ≫ f)
  have hφ : Spec.map φ = X.fromSpecResidueField z ≫ f := Spec.map_preimage _
  letI algz : Algebra κ (X.residueField z) := φ.hom.toAlgebra
  have hφ' : Spec.map (CommRingCat.ofHom (algebraMap κ (X.residueField z))) = X.fromSpecResidueField z ≫ f := by
    rw [← hφ]; rfl
  haveI : IsClosedImmersion (X.fromSpecResidueField z) := isClosed_singleton_iff_isClosedImmersion.mp hz
  have hfin : IsFinite (X.fromSpecResidueField z ≫ f) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  haveI : Module.Finite κ (X.residueField z) := by
    rw [← hφ] at hfin
    exact (IsFinite.SpecMap_iff φ).mp hfin

  let e : pullback (X.fromSpecResidueField z) (pullback.fst f s) ≅
      Spec (CommRingCat.of (X.residueField z ⊗[κ] Ω)) :=
    pullbackRightPullbackFstIso f s (X.fromSpecResidueField z) ≪≫
      pullback.congrHom hφ'.symm rfl ≪≫ pullbackSpecIso κ (X.residueField z) Ω
  haveI : IsArtinianRing (Ω ⊗[κ] X.residueField z) := IsArtinianRing.of_finite Ω _
  haveI : Finite (PrimeSpectrum (Ω ⊗[κ] X.residueField z)) := inferInstance
  haveI : Finite (PrimeSpectrum (X.residueField z ⊗[κ] Ω)) :=
    Finite.of_equiv _ (PrimeSpectrum.comapEquiv (Algebra.TensorProduct.comm κ (X.residueField z) Ω).toRingEquiv).toEquiv.symm
  haveI : Finite ↥(Spec (CommRingCat.of (X.residueField z ⊗[κ] Ω))) :=
    inferInstanceAs (Finite (PrimeSpectrum (X.residueField z ⊗[κ] Ω)))
  haveI : Finite ↥(pullback (X.fromSpecResidueField z) (pullback.fst f s)) :=
    Finite.of_equiv _ (Scheme.homeoOfIso e).symm.toEquiv
  exact Set.finite_range _

end S_AlgebraicGeometry_finite_setOf_pullback_fst_eq_of_isClosed_singleton
end P2MW
export P2MW.S_AlgebraicGeometry_finite_setOf_pullback_fst_eq_of_isClosed_singleton (solution)
