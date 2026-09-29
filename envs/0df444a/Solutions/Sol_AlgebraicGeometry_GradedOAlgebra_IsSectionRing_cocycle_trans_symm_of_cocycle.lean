-- Prove2me | solution 1 for AlgebraicGeometry.GradedOAlgebra.IsSectionRing.cocycle_trans_symm_of_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/8fe64469-b9d5-5c99-86e9-d9a2c0b5662b

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_exists_isSectionRing
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_algHom_apply_eq_pullback_of_isPullback
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_algHom_bijective_lift_tensorProduct_of_isPullback
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_ringHom_apply_eq_of_apply_eq_pullback
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_apply_comp_eq_pullback_comp_of_apply_eq_pullback
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_apply_eq_pullback_congr_hom
import Theorems.Thm_Algebra_TensorProduct_cocycle_trans_symm_of_comparison_identities
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullback_iso_trans_eq_of_cocycle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_cocycle_trans_symm_of_cocycle
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free PresheafOfModules.ExteriorPower.instModulePresheafAb"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules"
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem effdesc_exists_algebra_tower {S T A : Type u} [CommRing S] [CommRing T] [CommRing A] [Algebra S T]
    (iTA : Algebra T A) :
    ∃ (i : Algebra S A), @IsScalarTower S T A _ iTA.toSMul i.toSMul := by
  letI : Algebra S A := Algebra.compHom A (algebraMap S T)
  exact ⟨this, IsScalarTower.of_algebraMap_eq fun _ => rfl⟩

private theorem effdesc_exists_coface_algebras {S S'' T A : Type u} [CommRing S] [CommRing S''] [CommRing T] [CommRing A]
    [Algebra S S''] [Algebra S T] [Algebra S A] (iTA : Algebra T A) [@IsScalarTower S T A _ iTA.toSMul _]
    (g : S'' →ₐ[S] T) :
    ∃ (i₁ : Algebra S'' T) (i₂ : Algebra S'' A),
      @IsScalarTower S'' T A i₁.toSMul iTA.toSMul i₂.toSMul ∧ @IsScalarTower S S'' A _ i₂.toSMul _ ∧
      (∀ u, @algebraMap S'' T _ _ i₁ u = g u) ∧ (∀ u, @algebraMap S'' A _ _ i₂ u = algebraMap T A (g u)) := by
  letI i₁ : Algebra S'' T := g.toRingHom.toAlgebra
  letI i₂ : Algebra S'' A := ((algebraMap T A).comp g.toRingHom).toAlgebra
  refine ⟨i₁, i₂, IsScalarTower.of_algebraMap_eq fun _ => rfl, ?_, fun _ => rfl, fun _ => rfl⟩
  exact IsScalarTower.of_algebraMap_eq fun s => by
    change algebraMap S A s = algebraMap T A (g (algebraMap S S'' s))
    rw [AlgHom.commutes]
    exact IsScalarTower.algebraMap_apply S T A s

theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of S'))
    (L' : X'.Modules) (hL' : Scheme.Modules.IsInvertible L') (hva : Scheme.Modules.ClosedImmersionBySections L' f')
    (X'' : Scheme.{u}) (f'' : X'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S')))
    (a₁ a₂ : X'' ⟶ X')
    (ha₁ : IsPullback a₁ f'' f' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (X''' : Scheme.{u}) (f''' : X''' ⟶ Spec (CommRingCat.of (S' ⊗[S] (S' ⊗[S] S'))))
    (b₁₂ b₁₃ b₂₃ : X''' ⟶ X'')
    (hb₁₂ : IsPullback b₁₂ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')).toRingHom)))
    (hb₁₃ : IsPullback b₁₃ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S')).toRingHom)))
    (hb₂₃ : IsPullback b₂₃ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' ⊗[S] S' →ₐ[S] S' ⊗[S] (S' ⊗[S] S')).toRingHom)))
    (h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁) (h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁) (h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂)
    (ψ : (Scheme.Modules.pullback a₁).obj L' ≅ (Scheme.Modules.pullback a₂).obj L')
    (hψ : ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L') ≪≫
          ((Scheme.Modules.pullbackCongr h₂).app L') ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₂).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₃).app L').symm
        = ((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₃ a₂).app L'))
    (R' : Type u) [CommRing R'] [Algebra S' R'] [Algebra S R'] [IsScalarTower S S' R']
    (𝓡' : ℕ → Submodule S' R') [GradedAlgebra 𝓡']
    (ι' : ∀ n : ℕ, 𝓡' n → Γ(L'.tensorPow n, ⊤)) (hR' : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f' L' R' 𝓡' ι')
    (R'' : Type u) [CommRing R''] [Algebra (S' ⊗[S] S') R''] [Algebra S R''] [IsScalarTower S (S' ⊗[S] S') R'']
    (𝓡'' : ℕ → Submodule (S' ⊗[S] S') R'') [GradedAlgebra 𝓡'']
    (ι'' : ∀ n : ℕ, 𝓡'' n → Γ(((Scheme.Modules.pullback a₁).obj L').tensorPow n, ⊤))
    (hR'' : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f'' ((Scheme.Modules.pullback a₁).obj L') R'' 𝓡'' ι'')
    (ϑ₁ ϑ₂ : R' →ₐ[S] R'')
    (hϑ₁deg : ∀ n, ∀ x ∈ 𝓡' n, ϑ₁ x ∈ 𝓡'' n) (hϑ₂deg : ∀ n, ∀ x ∈ 𝓡' n, ϑ₂ x ∈ 𝓡'' n)
    (hϑ₁ : ∀ (n : ℕ) (x : 𝓡' n), ι'' n ⟨ϑ₁ x, hϑ₁deg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso a₁ L' n ≪≫
            Scheme.Modules.tensorPowMapIso (Iso.refl ((Scheme.Modules.pullback a₁).obj L')) n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction a₁).unit.app (L'.tensorPow n)).app ⊤) (ι' n x)))
    (hϑ₂ : ∀ (n : ℕ) (x : 𝓡' n), ι'' n ⟨ϑ₂ x, hϑ₂deg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso a₂ L' n ≪≫ Scheme.Modules.tensorPowMapIso ψ.symm n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction a₂).unit.app (L'.tensorPow n)).app ⊤) (ι' n x)))
    (hϑ₁lin : ∀ (s : S') (x : R'), ϑ₁ (s • x) = algebraMap (S' ⊗[S] S') R'' (s ⊗ₜ 1) * ϑ₁ x)
    (hϑ₂lin : ∀ (s : S') (x : R'), ϑ₂ (s • x) = algebraMap (S' ⊗[S] S') R'' (1 ⊗ₜ s) * ϑ₂ x)
    (β₁ : R' ⊗[S] S' ≃ₐ[S] R'')
    (hβ₁ : ∀ (r : R') (t : S'), β₁ (r ⊗ₜ t) = ϑ₁ r * algebraMap (S' ⊗[S] S') R'' (1 ⊗ₜ t))
    (β₂ : S' ⊗[S] R' ≃ₐ[S] R'')
    (hβ₂ : ∀ (s : S') (r : R'), β₂ (s ⊗ₜ r) = algebraMap (S' ⊗[S] S') R'' (s ⊗ₜ 1) * ϑ₂ r) :
    let φ : R' ⊗[S] S' ≃ₐ[S] S' ⊗[S] R' := β₁.trans β₂.symm
    (Algebra.TensorProduct.map (AlgHom.id S S') φ.toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S' R' S').toAlgHom.comp
          (Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S'))) =
      (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.comm S R' S').toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S' R' S').toAlgHom.comp
          ((Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S')).comp
            ((Algebra.TensorProduct.assoc S S S R' S' S').symm.toAlgHom.comp
              ((Algebra.TensorProduct.map (AlgHom.id S R') (Algebra.TensorProduct.comm S S' S').toAlgHom).comp
                (Algebra.TensorProduct.assoc S S S R' S' S').toAlgHom)))) := by
  classical

  obtain ⟨N, 𝔓, h𝔓⟩ := hva
  haveI : IsClosedImmersion 𝔓.toProj := h𝔓
  haveI : IsProper f' := by rw [← 𝔓.toProj_π]; infer_instance

  have hL''' : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L')) := (hL'.pullback a₁).pullback b₁₂
  obtain ⟨R''', _, iR3, 𝓡''', _, ι''', hR'''⟩ :=
    AlgebraicGeometry.GradedOAlgebra.exists_isSectionRing f''' ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L')) hL'''
  obtain ⟨iS3, hst3⟩ := effdesc_exists_algebra_tower (S := S) iR3
  have hι''' : ∀ n, Function.Injective (ι''' n) := fun n => (hR'''.bijective n).1

  obtain ⟨σ₁₂, hσ₁₂deg, hσ₁₂f, hσ₁₂lin⟩ : ∃ (σ : R'' →ₐ[S] R''') (hdeg : ∀ n, ∀ x ∈ 𝓡'' n, σ x ∈ 𝓡''' n),
      (∀ (n : ℕ) (x : 𝓡'' n), ι''' n ⟨σ x, hdeg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso b₁₂ ((Scheme.Modules.pullback a₁).obj L') n ≪≫ Scheme.Modules.tensorPowMapIso (Iso.refl ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))) n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction b₁₂).unit.app (((Scheme.Modules.pullback a₁).obj L').tensorPow n)).app ⊤) (ι'' n x))) ∧
      σ.comp (IsScalarTower.toAlgHom S (S' ⊗[S] S') R'') = (IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''').comp (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')) := by
    obtain ⟨iA, iB, t1, t2, hg1, hg2⟩ := effdesc_exists_coface_algebras (S := S) iR3 (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S'))
    have hb : IsPullback b₁₂ f''' f'' (Spec.map (CommRingCat.ofHom (algebraMap (S' ⊗[S] S') (S' ⊗[S] (S' ⊗[S] S'))))) := by
      convert hb₁₂ using 3
      exact RingHom.ext hg1
    obtain ⟨θ, hdeg, hθ⟩ :=
      AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_algHom_apply_eq_pullback_of_isPullback (S := (S' ⊗[S] S')) (S' ⊗[S] (S' ⊗[S] S'))
        f'' f''' b₁₂ hb ((Scheme.Modules.pullback a₁).obj L') _ (Iso.refl ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))) R'' 𝓡'' ι'' hR'' R''' 𝓡''' ι''' hR'''
    refine ⟨θ.restrictScalars S, hdeg, hθ, AlgHom.ext fun u => ?_⟩
    change θ (algebraMap (S' ⊗[S] S') R'' u) = algebraMap (S' ⊗[S] (S' ⊗[S] S')) R''' ((Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')) u)
    exact (θ.commutes u).trans (hg2 u)

  obtain ⟨σ₁₃, hσ₁₃deg, hσ₁₃f, hσ₁₃lin⟩ : ∃ (σ : R'' →ₐ[S] R''') (hdeg : ∀ n, ∀ x ∈ 𝓡'' n, σ x ∈ 𝓡''' n),
      (∀ (n : ℕ) (x : 𝓡'' n), ι''' n ⟨σ x, hdeg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso b₁₃ ((Scheme.Modules.pullback a₁).obj L') n ≪≫ Scheme.Modules.tensorPowMapIso (((Scheme.Modules.pullbackComp b₁₃ a₁).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm) n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction b₁₃).unit.app (((Scheme.Modules.pullback a₁).obj L').tensorPow n)).app ⊤) (ι'' n x))) ∧
      σ.comp (IsScalarTower.toAlgHom S (S' ⊗[S] S') R'') = (IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''').comp (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S')) := by
    obtain ⟨iA, iB, t1, t2, hg1, hg2⟩ := effdesc_exists_coface_algebras (S := S) iR3 (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S'))
    have hb : IsPullback b₁₃ f''' f'' (Spec.map (CommRingCat.ofHom (algebraMap (S' ⊗[S] S') (S' ⊗[S] (S' ⊗[S] S'))))) := by
      convert hb₁₃ using 3
      exact RingHom.ext hg1
    obtain ⟨θ, hdeg, hθ⟩ :=
      AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_algHom_apply_eq_pullback_of_isPullback (S := (S' ⊗[S] S')) (S' ⊗[S] (S' ⊗[S] S'))
        f'' f''' b₁₃ hb ((Scheme.Modules.pullback a₁).obj L') _ (((Scheme.Modules.pullbackComp b₁₃ a₁).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm) R'' 𝓡'' ι'' hR'' R''' 𝓡''' ι''' hR'''
    refine ⟨θ.restrictScalars S, hdeg, hθ, AlgHom.ext fun u => ?_⟩
    change θ (algebraMap (S' ⊗[S] S') R'' u) = algebraMap (S' ⊗[S] (S' ⊗[S] S')) R''' ((Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S')) u)
    exact (θ.commutes u).trans (hg2 u)

  obtain ⟨σ₂₃, hσ₂₃deg, hσ₂₃f, hσ₂₃lin⟩ : ∃ (σ : R'' →ₐ[S] R''') (hdeg : ∀ n, ∀ x ∈ 𝓡'' n, σ x ∈ 𝓡''' n),
      (∀ (n : ℕ) (x : 𝓡'' n), ι''' n ⟨σ x, hdeg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso b₂₃ ((Scheme.Modules.pullback a₁).obj L') n ≪≫ Scheme.Modules.tensorPowMapIso (((Scheme.Modules.pullbackComp b₂₃ a₁).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₂).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ.symm) n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction b₂₃).unit.app (((Scheme.Modules.pullback a₁).obj L').tensorPow n)).app ⊤) (ι'' n x))) ∧
      σ.comp (IsScalarTower.toAlgHom S (S' ⊗[S] S') R'') = (IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''').comp (Algebra.TensorProduct.includeRight (R := S) (A := S') (B := S' ⊗[S] S')) := by
    obtain ⟨iA, iB, t1, t2, hg1, hg2⟩ := effdesc_exists_coface_algebras (S := S) iR3 (Algebra.TensorProduct.includeRight (R := S) (A := S') (B := S' ⊗[S] S'))
    have hb : IsPullback b₂₃ f''' f'' (Spec.map (CommRingCat.ofHom (algebraMap (S' ⊗[S] S') (S' ⊗[S] (S' ⊗[S] S'))))) := by
      convert hb₂₃ using 3
      exact RingHom.ext hg1
    obtain ⟨θ, hdeg, hθ⟩ :=
      AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_algHom_apply_eq_pullback_of_isPullback (S := (S' ⊗[S] S')) (S' ⊗[S] (S' ⊗[S] S'))
        f'' f''' b₂₃ hb ((Scheme.Modules.pullback a₁).obj L') _ (((Scheme.Modules.pullbackComp b₂₃ a₁).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₂).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ.symm) R'' 𝓡'' ι'' hR'' R''' 𝓡''' ι''' hR'''
    refine ⟨θ.restrictScalars S, hdeg, hθ, AlgHom.ext fun u => ?_⟩
    change θ (algebraMap (S' ⊗[S] S') R'' u) = algebraMap (S' ⊗[S] (S' ⊗[S] S')) R''' ((Algebra.TensorProduct.includeRight (R := S) (A := S') (B := S' ⊗[S] S')) u)
    exact (θ.commutes u).trans (hg2 u)

  have c12_1 := AlgebraicGeometry.GradedOAlgebra.apply_comp_eq_pullback_comp_of_apply_eq_pullback a₁ b₁₂ L' ((Scheme.Modules.pullback a₁).obj L') ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))
      (Iso.refl ((Scheme.Modules.pullback a₁).obj L')) (Iso.refl ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))) R' 𝓡' R'' 𝓡'' R''' 𝓡''' ι' ι'' ι''' ϑ₁.toRingHom hϑ₁deg σ₁₂.toRingHom hσ₁₂deg hϑ₁ hσ₁₂f
  have c12_2 := AlgebraicGeometry.GradedOAlgebra.apply_comp_eq_pullback_comp_of_apply_eq_pullback a₂ b₁₂ L' ((Scheme.Modules.pullback a₁).obj L') ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))
      ψ.symm (Iso.refl ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))) R' 𝓡' R'' 𝓡'' R''' 𝓡''' ι' ι'' ι''' ϑ₂.toRingHom hϑ₂deg σ₁₂.toRingHom hσ₁₂deg hϑ₂ hσ₁₂f
  have c13_1 := AlgebraicGeometry.GradedOAlgebra.apply_comp_eq_pullback_comp_of_apply_eq_pullback a₁ b₁₃ L' ((Scheme.Modules.pullback a₁).obj L') ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))
      (Iso.refl ((Scheme.Modules.pullback a₁).obj L')) (((Scheme.Modules.pullbackComp b₁₃ a₁).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm) R' 𝓡' R'' 𝓡'' R''' 𝓡''' ι' ι'' ι''' ϑ₁.toRingHom hϑ₁deg σ₁₃.toRingHom hσ₁₃deg hϑ₁ hσ₁₃f
  have c13_2 := AlgebraicGeometry.GradedOAlgebra.apply_comp_eq_pullback_comp_of_apply_eq_pullback a₂ b₁₃ L' ((Scheme.Modules.pullback a₁).obj L') ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))
      ψ.symm (((Scheme.Modules.pullbackComp b₁₃ a₁).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm) R' 𝓡' R'' 𝓡'' R''' 𝓡''' ι' ι'' ι''' ϑ₂.toRingHom hϑ₂deg σ₁₃.toRingHom hσ₁₃deg hϑ₂ hσ₁₃f
  have c23_1 := AlgebraicGeometry.GradedOAlgebra.apply_comp_eq_pullback_comp_of_apply_eq_pullback a₁ b₂₃ L' ((Scheme.Modules.pullback a₁).obj L') ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))
      (Iso.refl ((Scheme.Modules.pullback a₁).obj L')) (((Scheme.Modules.pullbackComp b₂₃ a₁).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₂).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ.symm) R' 𝓡' R'' 𝓡'' R''' 𝓡''' ι' ι'' ι''' ϑ₁.toRingHom hϑ₁deg σ₂₃.toRingHom hσ₂₃deg hϑ₁ hσ₂₃f
  have c23_2 := AlgebraicGeometry.GradedOAlgebra.apply_comp_eq_pullback_comp_of_apply_eq_pullback a₂ b₂₃ L' ((Scheme.Modules.pullback a₁).obj L') ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))
      ψ.symm (((Scheme.Modules.pullbackComp b₂₃ a₁).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₂).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ.symm) R' 𝓡' R'' 𝓡'' R''' 𝓡''' ι' ι'' ι''' ϑ₂.toRingHom hϑ₂deg σ₂₃.toRingHom hσ₂₃deg hϑ₂ hσ₂₃f

  have c12_1' := AlgebraicGeometry.GradedOAlgebra.apply_eq_pullback_congr_hom (b₁₂ ≫ a₁) (b₁₃ ≫ a₁) h₁ L' ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))
      (((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso (Iso.refl ((Scheme.Modules.pullback a₁).obj L')) ≪≫ (Iso.refl ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L')))) R' 𝓡' R''' 𝓡''' ι' ι''' (σ₁₂.toRingHom.comp ϑ₁.toRingHom) (fun n x hx => hσ₁₂deg n _ (hϑ₁deg n x hx)) c12_1
  have c12_2' := AlgebraicGeometry.GradedOAlgebra.apply_eq_pullback_congr_hom (b₁₂ ≫ a₂) (b₂₃ ≫ a₁) h₂ L' ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))
      (((Scheme.Modules.pullbackComp b₁₂ a₂).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ.symm ≪≫ (Iso.refl ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L')))) R' 𝓡' R''' 𝓡''' ι' ι''' (σ₁₂.toRingHom.comp ϑ₂.toRingHom) (fun n x hx => hσ₁₂deg n _ (hϑ₂deg n x hx)) c12_2
  have c13_2' := AlgebraicGeometry.GradedOAlgebra.apply_eq_pullback_congr_hom (b₁₃ ≫ a₂) (b₂₃ ≫ a₂) h₃ L' ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))
      (((Scheme.Modules.pullbackComp b₁₃ a₂).app L').symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso ψ.symm ≪≫ (((Scheme.Modules.pullbackComp b₁₃ a₁).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm)) R' 𝓡' R''' 𝓡''' ι' ι''' (σ₁₃.toRingHom.comp ϑ₂.toRingHom) (fun n x hx => hσ₁₃deg n _ (hϑ₂deg n x hx)) c13_2

  obtain ⟨isoA, isoB, isoC⟩ := AlgebraicGeometry.Scheme.Modules.pullback_iso_trans_eq_of_cocycle X' X'' X''' a₁ a₂ b₁₂ b₁₃ b₂₃
    h₁ h₂ h₃ L' ψ hψ

  have hA : ∀ x : R', σ₁₃ (ϑ₁ x) = σ₁₂ (ϑ₁ x) := AlgebraicGeometry.GradedOAlgebra.ringHom_apply_eq_of_apply_eq_pullback (b₁₃ ≫ a₁) L' ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))
      (((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso (Iso.refl ((Scheme.Modules.pullback a₁).obj L')) ≪≫ (((Scheme.Modules.pullbackComp b₁₃ a₁).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm)) (((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ (((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso (Iso.refl ((Scheme.Modules.pullback a₁).obj L')) ≪≫ (Iso.refl ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))))) isoA.symm R' 𝓡' R''' 𝓡''' ι' ι''' hι''' (σ₁₃.toRingHom.comp ϑ₁.toRingHom) (fun n x hx => hσ₁₃deg n _ (hϑ₁deg n x hx))
      (σ₁₂.toRingHom.comp ϑ₁.toRingHom) (fun n x hx => hσ₁₂deg n _ (hϑ₁deg n x hx)) c13_1 c12_1'
  have hB : ∀ x : R', σ₂₃ (ϑ₁ x) = σ₁₂ (ϑ₂ x) := AlgebraicGeometry.GradedOAlgebra.ringHom_apply_eq_of_apply_eq_pullback (b₂₃ ≫ a₁) L' ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))
      (((Scheme.Modules.pullbackComp b₂₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso (Iso.refl ((Scheme.Modules.pullback a₁).obj L')) ≪≫ (((Scheme.Modules.pullbackComp b₂₃ a₁).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₂).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ.symm)) (((Scheme.Modules.pullbackCongr h₂).app L').symm ≪≫ (((Scheme.Modules.pullbackComp b₁₂ a₂).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ.symm ≪≫ (Iso.refl ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))))) isoB.symm R' 𝓡' R''' 𝓡''' ι' ι''' hι''' (σ₂₃.toRingHom.comp ϑ₁.toRingHom) (fun n x hx => hσ₂₃deg n _ (hϑ₁deg n x hx))
      (σ₁₂.toRingHom.comp ϑ₂.toRingHom) (fun n x hx => hσ₁₂deg n _ (hϑ₂deg n x hx)) c23_1 c12_2'
  have hC : ∀ x : R', σ₂₃ (ϑ₂ x) = σ₁₃ (ϑ₂ x) := AlgebraicGeometry.GradedOAlgebra.ringHom_apply_eq_of_apply_eq_pullback (b₂₃ ≫ a₂) L' ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))
      (((Scheme.Modules.pullbackComp b₂₃ a₂).app L').symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso ψ.symm ≪≫ (((Scheme.Modules.pullbackComp b₂₃ a₁).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₂).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ.symm)) (((Scheme.Modules.pullbackCongr h₃).app L').symm ≪≫ (((Scheme.Modules.pullbackComp b₁₃ a₂).app L').symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso ψ.symm ≪≫ (((Scheme.Modules.pullbackComp b₁₃ a₁).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm))) isoC.symm R' 𝓡' R''' 𝓡''' ι' ι''' hι''' (σ₂₃.toRingHom.comp ϑ₂.toRingHom) (fun n x hx => hσ₂₃deg n _ (hϑ₂deg n x hx))
      (σ₁₃.toRingHom.comp ϑ₂.toRingHom) (fun n x hx => hσ₁₃deg n _ (hϑ₂deg n x hx)) c23_2 c13_2'

  have hq : IsPullback (b₁₂ ≫ a₁) f''' f'
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] (S' ⊗[S] S')).toRingHom)) := by
    have hp := hb₁₂.paste_horiz ha₁
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at hp
    convert hp using 3 <;> try rfl
  obtain ⟨ρ, hρdeg, hρ, -, -, hρbij⟩ :=
    AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_algHom_bijective_lift_tensorProduct_of_isPullback S' (S' ⊗[S] S') f' f'''
      (b₁₂ ≫ a₁) hq L' hL' ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L')) (((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso (Iso.refl ((Scheme.Modules.pullback a₁).obj L')) ≪≫ (Iso.refl ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L')))) R' 𝓡' ι' hR' R''' 𝓡''' ι''' hR'''
  have hρeq : ∀ x : R', ρ x = σ₁₂ (ϑ₁ x) :=
    AlgebraicGeometry.GradedOAlgebra.ringHom_apply_eq_of_apply_eq_pullback (b₁₂ ≫ a₁) L' ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))
      (((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso (Iso.refl ((Scheme.Modules.pullback a₁).obj L')) ≪≫ (Iso.refl ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L')))) (((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso (Iso.refl ((Scheme.Modules.pullback a₁).obj L')) ≪≫ (Iso.refl ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L')))) rfl R' 𝓡' R''' 𝓡''' ι' ι''' hι''' ρ.toRingHom hρdeg
      (σ₁₂.toRingHom.comp ϑ₁.toRingHom) (fun n x hx => hσ₁₂deg n _ (hϑ₁deg n x hx)) hρ c12_1
  have hρ' : ρ = σ₁₂.comp ϑ₁ := AlgHom.ext hρeq
  subst hρ'

  exact Algebra.TensorProduct.cocycle_trans_symm_of_comparison_identities S' R' R'' R''' ϑ₁ ϑ₂ β₁ hβ₁ β₂ hβ₂ σ₁₂ σ₁₃ σ₂₃
    hσ₁₂lin hσ₁₃lin hσ₂₃lin hA hB hC hρbij

end S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_cocycle_trans_symm_of_cocycle
end P2MW
export P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_cocycle_trans_symm_of_cocycle (solution)
