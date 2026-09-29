-- Prove2me | solution 1 for AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_algHom_bijective_lift_of_isPullback_includeRight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/66033381-4d15-5270-bd9a-f9255d65aac2

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_algHom_apply_eq_pullback_of_isPullback
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_isBaseChange_of_apply_eq_pullback_of_flat
import Theorems.Thm_GradedAlgebra_bijective_tensorProduct_lift_of_forall_isBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_algHom_bijective_lift_of_isPullback_includeRight
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free PresheafOfModules.ExteriorPower.instModulePresheafAb"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules"
open scoped TensorProduct

private theorem coface_second_transport
    {S : Type u} [CommRing S] (S' T : Type u) [CommRing S'] [CommRing T] [Algebra S S'] [Algebra S T]
    (R' : Type u) [CommRing R'] [Algebra T R'] [Algebra S R'] [IsScalarTower S T R']
    (𝓡' : ℕ → Submodule T R') [GradedAlgebra 𝓡']
    (R'' : Type u) [CommRing R''] [Algebra (S' ⊗[S] T) R''] [Algebra S R''] [IsScalarTower S (S' ⊗[S] T) R'']
    [Algebra T R'']
    [@IsScalarTower T (S' ⊗[S] T) R'' (Algebra.TensorProduct.rightAlgebra (R := S) (A := S') (B := T)).toSMul
      inferInstance inferInstance]
    [IsScalarTower S T R'']
    (𝓡'' : ℕ → Submodule (S' ⊗[S] T) R'') [GradedAlgebra 𝓡'']
    (θ : R' →ₐ[T] R'') (hθdeg : ∀ n, ∀ x ∈ 𝓡' n, θ x ∈ 𝓡'' n)
    (hbc : letI := Algebra.TensorProduct.rightAlgebra (R := S) (A := S') (B := T)
      ∀ n, IsBaseChange (S' ⊗[S] T) ((θ.toLinearMap.restrict (p := 𝓡' n) (q := (𝓡'' n).restrictScalars T) (hθdeg n))
        : 𝓡' n →ₗ[T] (𝓡'' n).restrictScalars T)) :
    Function.Bijective
      (Algebra.TensorProduct.lift
        ((IsScalarTower.toAlgHom S (S' ⊗[S] T) R'').comp (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] T))
        (θ.restrictScalars S) (fun _ _ => Commute.all _ _) : S' ⊗[S] R' →ₐ[S] R'') := by
  letI instR := Algebra.TensorProduct.rightAlgebra (R := S) (A := S') (B := T)
  have hbij := GradedAlgebra.bijective_tensorProduct_lift_of_forall_isBaseChange (S' ⊗[S] T) R' 𝓡' R'' 𝓡'' θ hθdeg hbc

  let eR : (S' ⊗[S] T) ≃ₗ[T] (T ⊗[S] S') :=
    { toFun := TensorProduct.comm S S' T
      invFun := (TensorProduct.comm S S' T).symm
      map_add' := fun x y => map_add _ x y
      map_smul' := fun t x => by
        show TensorProduct.comm S S' T (((1 : S') ⊗ₜ[S] t) * x) = t • TensorProduct.comm S S' T x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul u v =>
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.comm_tmul, TensorProduct.comm_tmul,
            TensorProduct.smul_tmul', smul_eq_mul]
        | add x y hx hy => rw [mul_add, map_add, hx, hy, map_add, smul_add]
      left_inv := fun x => (TensorProduct.comm S S' T).symm_apply_apply x
      right_inv := fun x => (TensorProduct.comm S S' T).apply_symm_apply x }
  have heR : ∀ (u : T) (v : S'), eR.symm (u ⊗ₜ v) = v ⊗ₜ u := fun _ _ => rfl
  let κ₁ := TensorProduct.comm S S' R'
  let κ₂ := (Algebra.TensorProduct.cancelBaseChange S T T R' S').symm
  let κ₃ := LinearEquiv.lTensor R' eR.symm
  have hfun : ⇑(Algebra.TensorProduct.lift
        ((IsScalarTower.toAlgHom S (S' ⊗[S] T) R'').comp (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] T))
        (θ.restrictScalars S) (fun _ _ => Commute.all _ _) : S' ⊗[S] R' →ₐ[S] R'') =
      ⇑(Algebra.TensorProduct.lift θ (IsScalarTower.toAlgHom T (S' ⊗[S] T) R'') (fun _ _ => Commute.all _ _)) ∘
        ⇑κ₃ ∘ ⇑κ₂ ∘ ⇑κ₁ := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp only [Function.comp_apply, map_zero]
    | tmul s r =>
      simp only [Function.comp_apply, κ₁, κ₂, κ₃, TensorProduct.comm_tmul,
        Algebra.TensorProduct.cancelBaseChange_symm_tmul, LinearEquiv.lTensor_tmul, heR, Algebra.TensorProduct.lift_tmul,
        AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_restrictScalars', IsScalarTower.coe_toAlgHom',
        Algebra.TensorProduct.includeLeft_apply]
      rw [mul_comm]
    | add z₁ z₂ h₁ h₂ =>
      simp only [Function.comp_apply] at h₁ h₂
      simp only [Function.comp_apply, _root_.map_add, h₁, h₂]
  rw [hfun]
  exact hbij.comp (κ₃.bijective.comp (κ₂.bijective.comp κ₁.bijective))

theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.Flat S S']
    {X' X'' : Scheme.{u}} (f' : X' ⟶ Spec (CommRingCat.of S')) [QuasiCompact f'] [IsSeparated f']
    (f'' : X'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (a : X'' ⟶ X')
    (ha : IsPullback a f'' f' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (L' : X'.Modules) (hL' : Scheme.Modules.IsInvertible L') (L'' : X''.Modules) (e : (Scheme.Modules.pullback a).obj L' ≅ L'')
    (R' : Type u) [CommRing R'] [Algebra S' R'] [Algebra S R'] [IsScalarTower S S' R']
    (𝓡' : ℕ → Submodule S' R') [GradedAlgebra 𝓡']
    (ι' : ∀ n : ℕ, 𝓡' n → Γ(L'.tensorPow n, ⊤)) (hR' : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f' L' R' 𝓡' ι')
    (R'' : Type u) [CommRing R''] [Algebra (S' ⊗[S] S') R''] [Algebra S R''] [IsScalarTower S (S' ⊗[S] S') R'']
    (𝓡'' : ℕ → Submodule (S' ⊗[S] S') R'') [GradedAlgebra 𝓡'']
    (ι'' : ∀ n : ℕ, 𝓡'' n → Γ(L''.tensorPow n, ⊤)) (hR'' : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f'' L'' R'' 𝓡'' ι'') :
    ∃ (ϑ : R' →ₐ[S] R'') (hϑdeg : ∀ n, ∀ x ∈ 𝓡' n, ϑ x ∈ 𝓡'' n),
      (∀ (n : ℕ) (x : 𝓡' n), ι'' n ⟨ϑ x, hϑdeg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso a L' n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app (L'.tensorPow n)).app ⊤) (ι' n x))) ∧
      (∀ (s : S') (x : R'), ϑ (s • x) = algebraMap (S' ⊗[S] S') R'' (1 ⊗ₜ s) * ϑ x) ∧
      (∀ n, 𝓡'' n ≤ Submodule.span (S' ⊗[S] S') (ϑ '' (𝓡' n : Set R'))) ∧
      Function.Bijective
        (Algebra.TensorProduct.lift
          ((IsScalarTower.toAlgHom S (S' ⊗[S] S') R'').comp (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')) ϑ
          (fun _ _ => Commute.all _ _) : S' ⊗[S] R' →ₐ[S] R'') := by
  classical

  letI instR : Algebra S' (S' ⊗[S] S') := Algebra.TensorProduct.rightAlgebra

  have hflat' : (algebraMap S' (S' ⊗[S] S')).Flat :=
    @RingHom.Flat.isStableUnderBaseChange S S' S' (S' ⊗[S] S') _ _ _ _ _ _ _
      Algebra.TensorProduct.leftAlgebra instR _ Algebra.TensorProduct.right_isScalarTower
      TensorProduct.isPushout (RingHom.flat_algebraMap_iff.mpr inferInstance)
  haveI hflat := RingHom.flat_algebraMap_iff.mp hflat'

  letI : Algebra S' R'' :=
    ((algebraMap (S' ⊗[S] S') R'').comp (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom).toAlgebra
  haveI hst := IsScalarTower.of_algebraMap_eq (R := S') (S := S' ⊗[S] S') (A := R'') (fun _ => rfl)
  haveI : IsScalarTower S S' R'' :=
    IsScalarTower.of_algebraMap_eq (R := S) (S := S') (A := R'') (fun s => by
      change algebraMap S R'' s = algebraMap (S' ⊗[S] S') R'' ((1 : S') ⊗ₜ[S] algebraMap S S' s)
      rw [IsScalarTower.algebraMap_apply S (S' ⊗[S] S') R'' s]
      congr 1
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul])

  obtain ⟨θ, hθdeg, hθ⟩ :=
    AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_algHom_apply_eq_pullback_of_isPullback (S' ⊗[S] S') f' f'' a ha
      L' L'' e R' 𝓡' ι' hR' R'' 𝓡'' ι'' hR''
  have hbc := fun n =>
    AlgebraicGeometry.GradedOAlgebra.IsSectionRing.isBaseChange_of_apply_eq_pullback_of_flat (S' ⊗[S] S') f' f'' a ha
      L' hL' L'' e R' 𝓡' ι' hR' R'' 𝓡'' ι'' hR'' θ hθdeg hθ n
  refine ⟨θ.restrictScalars S, hθdeg, hθ, ?_, ?_, ?_⟩
  ·
    intro s x
    change θ (s • x) = _
    rw [Algebra.smul_def, _root_.map_mul, AlgHom.commutes]; rfl
  ·
    intro n y hy
    obtain ⟨t, ht⟩ := (hbc n).equiv.surjective ⟨y, hy⟩
    rw [show y = ((hbc n).equiv t : R'') by rw [ht]]
    clear ht
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul u x =>
      rw [IsBaseChange.equiv_tmul]
      change u • (θ (x : R')) ∈ _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, x.2, rfl⟩)
    | add t₁ t₂ h₁ h₂ =>
      rw [_root_.map_add, Submodule.coe_add]
      exact Submodule.add_mem _ h₁ h₂
  ·
    exact coface_second_transport S' S' R' 𝓡' R'' 𝓡'' θ hθdeg hbc

end S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_algHom_bijective_lift_of_isPullback_includeRight
end P2MW
export P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_algHom_bijective_lift_of_isPullback_includeRight (solution)
