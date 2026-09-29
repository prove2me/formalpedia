-- Prove2me | solution 1 for AlgebraicGeometry.DescentAction.effective_of_finiteEtale_of_forall_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/91305d46-af0b-5101-b6ee-8ad457fdd21e

import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentAction
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation
import Theorems.Thm_AlgebraicGeometry_DescentAction_effective_of_isPullback_of_flat_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_DescentAction_effective_of_finiteEtale_of_forall_orbit

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem solution
    (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    {X' : Scheme.{u}} {x' : X' ⟶ Spec (CommRingCat.of R')}
    (A : DescentAction (Spec.map (CommRingCat.ofHom (algebraMap R R'))) x')
    (haff : ∀ x : X', ∃ U : X'.Opens, IsAffineOpen U ∧
      ∀ r : ↑(pullback (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R R')))),
        (pullback.fst (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R R')))) r = x → A.act r ∈ U) :
    A.Effective := by
  classical

  have hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (by
      change RingHom.Flat (algebraMap R R'); exact RingHom.flat_algebraMap_iff.2 inferInstance)
  have hfin : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    (IsFinite.SpecMap_iff _).2 (by change (algebraMap R R').Finite; exact RingHom.finite_algebraMap.mpr inferInstance)
  have hlofp : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2 (by
      change (algebraMap R R').FinitePresentation
      exact RingHom.finitePresentation_algebraMap.mpr inferInstance)
  haveI := hflat; haveI := hfin; haveI := hlofp

  haveI : IsFinite (pullback.fst (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (Spec.map (CommRingCat.ofHom (algebraMap R R')))) := MorphismProperty.pullback_fst _ _ hfin
  haveI : Flat (pullback.fst (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (Spec.map (CommRingCat.ofHom (algebraMap R R')))) := MorphismProperty.pullback_fst _ _ hflat
  haveI : LocallyOfFinitePresentation (pullback.fst (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (Spec.map (CommRingCat.ofHom (algebraMap R R')))) := MorphismProperty.pullback_fst _ _ hlofp
  haveI : IsFinite A.act := by rw [A.act_eq_invol_fst]; infer_instance
  haveI : Flat A.act := by rw [A.act_eq_invol_fst]; infer_instance
  haveI : LocallyOfFinitePresentation A.act := by rw [A.act_eq_invol_fst]; infer_instance

  obtain ⟨Y, p, w, _, hpflat, _, hpsurj, hR, ⟨hcolim⟩⟩ :=
    AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation
      (pullback.fst (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
        (Spec.map (CommRingCat.ofHom (algebraMap R R')))) A.act
      (fun a b h₁ h₂ => A.hom_ext h₁ h₂) (fun T => A.equivalence T) haff
  haveI := hpflat; haveI := hpsurj
  haveI : QuasiCompact p := inferInstance

  have hco : pullback.fst (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≫ x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) =
      A.act ≫ x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
    rw [pullback.condition, reassoc_of% A.act_comp]
  obtain ⟨f, hpf⟩ := Cofork.IsColimit.desc' hcolim (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) hco

  obtain ⟨e, he, -, hc⟩ := AlgebraicGeometry.DescentAction.effective_of_isPullback_of_flat_surjective
    (Spec.map (CommRingCat.ofHom (algebraMap R R'))) A p w hR f hpf
  exact ⟨Y, f, e, he, hc⟩

end S_AlgebraicGeometry_DescentAction_effective_of_finiteEtale_of_forall_orbit
end P2MW
export P2MW.S_AlgebraicGeometry_DescentAction_effective_of_finiteEtale_of_forall_orbit (solution)
