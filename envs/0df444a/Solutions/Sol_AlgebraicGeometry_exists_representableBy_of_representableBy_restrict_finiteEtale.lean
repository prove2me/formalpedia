-- Prove2me | solution 1 for AlgebraicGeometry.exists_representableBy_of_representableBy_restrict_finiteEtale
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/8f5e066f-dccc-552b-a199-2d84aac32ef6

import Definitions.Def_AlgebraicGeometry_DescentAction
import Theorems.Thm_AlgebraicGeometry_DescentAction_effective_of_finiteEtale
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_representableBy_of_representableBy_restrict_finiteEtale

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem solution
    (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type (u + 1))
    (hG : ∀ T : Over (Spec (CommRingCat.of R)), Presieve.IsSheafFor G (Presieve.singleton
      ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap R R')))).counit.app T)))
    {X' : Scheme.{u}} (x' : X' ⟶ Spec (CommRingCat.of R'))
    (hX' : ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap R R')))).op ⋙ G).RepresentableBy (Over.mk x'))
    (haff : ∀ S : Finset X', ∃ U : X'.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) (_ : G.RepresentableBy (Over.mk f))
      (e : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≅ X'),
      e.hom ≫ x' = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by

  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (by
      change RingHom.Flat (algebraMap R R')
      exact RingHom.flat_algebraMap_iff.2 inferInstance)
  haveI : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := ⟨by
    change Function.Surjective (PrimeSpectrum.comap (algebraMap R R'))
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩

  obtain ⟨X, f, e, he, hc⟩ := AlgebraicGeometry.DescentAction.effective_of_finiteEtale R R'
    (DescentAction.ofRepresentableBy _ G x' hX') haff

  have hG' : ∀ T : Over (Spec (CommRingCat.of R)), Presieve.IsSheafFor G
      (Presieve.singleton (DescentAction.coverT (Spec.map (CommRingCat.ofHom (algebraMap R R'))) T)) := fun T => by
    rw [← DescentAction.counit_app_eq_coverT]
    exact hG T
  obtain ⟨rep⟩ := DescentAction.representableBy_of_compatible _ G x' hX' f e he hG' hc
  exact ⟨X, f, rep, e, he⟩

end S_AlgebraicGeometry_exists_representableBy_of_representableBy_restrict_finiteEtale
end P2MW
export P2MW.S_AlgebraicGeometry_exists_representableBy_of_representableBy_restrict_finiteEtale (solution)
