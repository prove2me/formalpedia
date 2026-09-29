-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RigidifiedLineBundle.fibrewiseAlgEquivZero_of_pullback_finite_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8ef400aa-ee63-5158-bc9c-319f6f6947a5

import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_pullback_finite_faithfullyFlat

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra

open scoped TensorProduct

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Module.FaithfullyFlat R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
    (h : FibrewiseAlgEquivZero (M.pullbackAlong ⟨pullback.fst t (specMap R R'), pullback.condition⟩)) :
    FibrewiseAlgEquivZero M := by
  intro k _ _ σ

  obtain ⟨σ', hσ'⟩ : ∃ σ' : Spec (CommRingCat.of k) ⟶ pullback t (specMap R R'),
      σ' ≫ pullback.fst t (specMap R R') = σ := by

    let ρ : CommRingCat.of R ⟶ CommRingCat.of k := (Spec.fullyFaithful.preimage (σ ≫ t)).unop
    have hρ : Spec.map ρ = σ ≫ t := Spec.fullyFaithful.map_preimage (σ ≫ t)
    letI : Algebra R k := ρ.hom.toAlgebra

    haveI : Nontrivial (k ⊗[R] R') := inferInstance
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (k ⊗[R] R')
    letI : Field ((k ⊗[R] R') ⧸ m) := Ideal.Quotient.field m
    haveI : Module.Finite k ((k ⊗[R] R') ⧸ m) := inferInstance
    haveI : Algebra.IsIntegral k ((k ⊗[R] R') ⧸ m) := Algebra.IsIntegral.of_finite k _
    have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := (k ⊗[R] R') ⧸ m)
    let ι : ((k ⊗[R] R') ⧸ m) ≃+* k := (RingEquiv.ofBijective (algebraMap k ((k ⊗[R] R') ⧸ m)) hbij).symm
    let g : R' →+* k :=
      ι.toRingHom.comp ((Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := R) (A := k)).toRingHom)
    have hg : g.comp (algebraMap R R') = ρ.hom := by
      ext r
      change ι (Ideal.Quotient.mk m (Algebra.TensorProduct.includeRight (R := R) (A := k) (algebraMap R R' r))) =
        algebraMap R k r
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R k (k ⊗[R] R'), ← Ideal.Quotient.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply]
      exact (RingEquiv.ofBijective (algebraMap k ((k ⊗[R] R') ⧸ m)) hbij).symm_apply_apply _
    let τ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R') := Spec.map (CommRingCat.ofHom g)
    have hτ : σ ≫ t = τ ≫ specMap R R' := by
      rw [← hρ]
      change Spec.map ρ = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hg, CommRingCat.ofHom_hom]
    exact ⟨pullback.lift σ τ hτ, pullback.lift_fst _ _ _⟩

  set ψ : SchemeHomOver (pullback.snd t (specMap R R') ≫ specMap R R') t :=
    ⟨pullback.fst t (specMap R R'), pullback.condition⟩ with hψ

  have w : (pullback.fst (pullback.snd c t) σ ≫ pullback.fst c t) ≫ c =
      (pullback.snd (pullback.snd c t) σ ≫ σ') ≫ (pullback.snd t (specMap R R') ≫ specMap R R') := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc,
      ← pullback.condition, reassoc_of% hσ']
  let a : pullback (pullback.snd c t) σ ⟶ pullback c (pullback.snd t (specMap R R') ≫ specMap R R') :=
    pullback.lift _ _ w
  let e' : pullback (pullback.snd c t) σ ⟶ pullback (pullback.snd c (pullback.snd t (specMap R R') ≫ specMap R R')) σ' :=
    pullback.lift a (pullback.snd _ _) (pullback.lift_snd _ _ _)
  have he' : e' ≫ fibreAt c (pullback.snd t (specMap R R') ≫ specMap R R') σ' = fibreAt c t σ := by
    simp only [e', fibreAt, pullback.lift_snd]
  have ha : a ≫ baseChangeSnd c ψ = pullback.fst (pullback.snd c t) σ := by
    apply pullback.hom_ext
    · simp only [a, baseChangeSnd, Category.assoc, pullback.lift_fst, Category.comp_id]
    · simp only [a, baseChangeSnd, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      change pullback.snd (pullback.snd c t) σ ≫ σ' ≫ pullback.fst t (specMap R R') = _
      rw [hσ']
      exact pullback.condition.symm
  have hcomp : (e' ≫ pullback.fst (pullback.snd c (pullback.snd t (specMap R R') ≫ specMap R R')) σ') ≫
      baseChangeSnd c ψ = pullback.fst (pullback.snd c t) σ := by
    rw [show e' ≫ pullback.fst _ _ = a from pullback.lift_fst _ _ _, ha]
  refine IsAlgEquivZero.of_iso ?_ ((h k σ').pullback e' he')
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr hcomp).app M.L

end S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_pullback_finite_faithfullyFlat
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_pullback_finite_faithfullyFlat (solution)
