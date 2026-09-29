-- Prove2me | solution 1 for AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_algHom_bijective_lift_of_isPullback_includeLeft
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/dde5166a-f8a7-58f0-8ed8-7c0beeb6599b

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_algHom_apply_eq_pullback_of_isPullback
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_isBaseChange_of_apply_eq_pullback_of_flat
import Theorems.Thm_GradedAlgebra_bijective_tensorProduct_lift_of_forall_isBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_algHom_bijective_lift_of_isPullback_includeLeft
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free PresheafOfModules.ExteriorPower.instModulePresheafAb"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules"
open scoped TensorProduct

theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.Flat S S']
    {X' X'' : Scheme.{u}} (f' : X' ⟶ Spec (CommRingCat.of S')) [QuasiCompact f'] [IsSeparated f']
    (f'' : X'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (a : X'' ⟶ X')
    (ha : IsPullback a f'' f' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
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
      (∀ (s : S') (x : R'), ϑ (s • x) = algebraMap (S' ⊗[S] S') R'' (s ⊗ₜ 1) * ϑ x) ∧
      (∀ n, 𝓡'' n ≤ Submodule.span (S' ⊗[S] S') (ϑ '' (𝓡' n : Set R'))) ∧
      Function.Bijective
        (Algebra.TensorProduct.lift ϑ
          ((IsScalarTower.toAlgHom S (S' ⊗[S] S') R'').comp (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S'))
          (fun _ _ => Commute.all _ _) : R' ⊗[S] S' →ₐ[S] R'') := by
  classical

  have hincl : (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom = algebraMap S' (S' ⊗[S] S') :=
    RingHom.ext fun _ => rfl
  have ha' : IsPullback a f'' f' (Spec.map (CommRingCat.ofHom (algebraMap S' (S' ⊗[S] S')))) := by
    rw [← hincl]; exact ha

  letI : Algebra S' R'' := ((algebraMap (S' ⊗[S] S') R'').comp (algebraMap S' (S' ⊗[S] S'))).toAlgebra
  haveI : IsScalarTower S' (S' ⊗[S] S') R'' :=
    IsScalarTower.of_algebraMap_eq (R := S') (S := S' ⊗[S] S') (A := R'') (fun _ => rfl)
  haveI : IsScalarTower S S' R'' :=
    IsScalarTower.of_algebraMap_eq (R := S) (S := S') (A := R'') (fun s => by
      change algebraMap S R'' s = algebraMap (S' ⊗[S] S') R'' (algebraMap S' (S' ⊗[S] S') (algebraMap S S' s))
      rw [← IsScalarTower.algebraMap_apply S S' (S' ⊗[S] S') s, ← IsScalarTower.algebraMap_apply S (S' ⊗[S] S') R'' s])

  obtain ⟨θ, hθdeg, hθ⟩ :=
    AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_algHom_apply_eq_pullback_of_isPullback (S' ⊗[S] S') f' f'' a ha'
      L' L'' e R' 𝓡' ι' hR' R'' 𝓡'' ι'' hR''
  have hbc := fun n =>
    AlgebraicGeometry.GradedOAlgebra.IsSectionRing.isBaseChange_of_apply_eq_pullback_of_flat (S' ⊗[S] S') f' f'' a ha'
      L' hL' L'' e R' 𝓡' ι' hR' R'' 𝓡'' ι'' hR'' θ hθdeg hθ n

  have hbij := GradedAlgebra.bijective_tensorProduct_lift_of_forall_isBaseChange (S' ⊗[S] S') R' 𝓡' R'' 𝓡'' θ hθdeg hbc
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
    let κ := Algebra.TensorProduct.cancelBaseChange S S' S' R' S'
    have hfun : ⇑(Algebra.TensorProduct.lift (θ.restrictScalars S)
          ((IsScalarTower.toAlgHom S (S' ⊗[S] S') R'').comp (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S'))
          (fun _ _ => Commute.all _ _) : R' ⊗[S] S' →ₐ[S] R'') =
        ⇑(Algebra.TensorProduct.lift θ (IsScalarTower.toAlgHom S' (S' ⊗[S] S') R'') (fun _ _ => Commute.all _ _)) ∘ ⇑κ.symm := by
      funext z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul r t => simp [κ, Algebra.TensorProduct.lift_tmul]
      | add z₁ z₂ h₁ h₂ => simp only [_root_.map_add, Function.comp_apply] at h₁ h₂ ⊢; rw [h₁, h₂]
    rw [hfun]
    exact hbij.comp κ.symm.bijective

end S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_algHom_bijective_lift_of_isPullback_includeLeft
end P2MW
export P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_algHom_bijective_lift_of_isPullback_includeLeft (solution)
