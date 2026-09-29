-- Prove2me | solution 1 for AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/3218c9a3-d140-52be-ab25-40c2865727b6

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_exists_isSectionRing
import Theorems.Thm_Algebra_bijective_tensorProduct_equalizer_of_faithfullyFlat_of_cocycle
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_isCanonicalToProj
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_isIso
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_comp_map_eq_comp
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_isPullback_projMap_of_isBaseChange
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isInvertible_pullback_iso_of_cocycle_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
import Theorems.Thm_GradedAlgebra_bijective_tensorProduct_lift_of_forall_isBaseChange
import Theorems.Thm_Subalgebra_exists_gradedAlgebra_isBaseChange_of_bijective_of_decompose_mem
import Theorems.Thm_HomogeneousIdeal_irrelevant_le_map_of_forall_le_span_image
import Theorems.Thm_Algebra_TensorProduct_descent_datum_trans_symm_of_apply_tmul
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_algHom_bijective_lift_of_isPullback_includeLeft
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_algHom_bijective_lift_of_isPullback_includeRight
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_cocycle_trans_symm_of_cocycle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_descent_of_faithfullyFlat_of_cocycle
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free PresheafOfModules.ExteriorPower.instModulePresheafAb"
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app Algebra.DescentCofaces.i₁_apply Algebra.DescentCofaces.i₂_apply Algebra.DescentCofaces.c₁₂_tmul Algebra.DescentCofaces.c₂₃_tmul Algebra.DescentCofaces.c₁₃_tmul AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc"
p2m_attr_erase "simp" "AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization"
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

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
        = ((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₃ a₂).app L')) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of S)) (c : X' ⟶ X)
      (_ : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S')))),
      a₁ ≫ c = a₂ ≫ c ∧
      ∃ (L : X.Modules), Scheme.Modules.IsInvertible L ∧
        Nonempty ((Scheme.Modules.pullback c).obj L ≅ L') := by
  classical

  obtain ⟨N, 𝔓, h𝔓⟩ := hva
  haveI : IsClosedImmersion 𝔓.toProj := h𝔓
  haveI : IsProper f' := by rw [← 𝔓.toProj_π]; infer_instance
  have hva' : Scheme.Modules.ClosedImmersionBySections L' f' := ⟨N, 𝔓, h𝔓⟩

  have hincl : (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom = algebraMap S' (S' ⊗[S] S') :=
    RingHom.ext fun _ => rfl
  have ha₁' : IsPullback a₁ f'' f' (Spec.map (CommRingCat.ofHom (algebraMap S' (S' ⊗[S] S')))) := by
    rw [← hincl]; exact ha₁

  obtain ⟨R', _, _, 𝓡', _, ι', hR'⟩ := AlgebraicGeometry.GradedOAlgebra.exists_isSectionRing f' L' hL'
  letI : Algebra S R' := ((algebraMap S' R').comp (algebraMap S S')).toAlgebra
  haveI : IsScalarTower S S' R' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hL'' : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback a₁).obj L') := hL'.pullback a₁
  obtain ⟨R'', _, _, 𝓡'', _, ι'', hR''⟩ :=
    AlgebraicGeometry.GradedOAlgebra.exists_isSectionRing f'' ((Scheme.Modules.pullback a₁).obj L') hL''
  letI : Algebra S R'' := ((algebraMap (S' ⊗[S] S') R'').comp (algebraMap S (S' ⊗[S] S'))).toAlgebra
  haveI : IsScalarTower S (S' ⊗[S] S') R'' :=
    IsScalarTower.of_algebraMap_eq (R := S) (S := S' ⊗[S] S') (A := R'') (fun _ => rfl)

  obtain ⟨ϑ₁, hϑ₁deg, hϑ₁, hϑ₁lin, hspan₁, hbij₁⟩ :=
    AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_algHom_bijective_lift_of_isPullback_includeLeft
      S' f' f'' a₁ ha₁ L' hL' _ (Iso.refl _) R' 𝓡' ι' hR' R'' 𝓡'' ι'' hR''
  obtain ⟨ϑ₂, hϑ₂deg, hϑ₂, hϑ₂lin, hspan₂, hbij₂⟩ :=
    AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_algHom_bijective_lift_of_isPullback_includeRight
      S' f' f'' a₂ ha₂ L' hL' _ ψ.symm R' 𝓡' ι' hR' R'' 𝓡'' ι'' hR''
  set β₁ : R' ⊗[S] S' ≃ₐ[S] R'' := AlgEquiv.ofBijective _ hbij₁ with hβ₁def
  set β₂ : S' ⊗[S] R' ≃ₐ[S] R'' := AlgEquiv.ofBijective _ hbij₂ with hβ₂def
  have hβ₁ : ∀ (r : R') (t : S'), β₁ (r ⊗ₜ t) = ϑ₁ r * algebraMap (S' ⊗[S] S') R'' (1 ⊗ₜ t) := by
    intro r t; simp [hβ₁def, Algebra.TensorProduct.lift_tmul]
  have hβ₂ : ∀ (s : S') (r : R'), β₂ (s ⊗ₜ r) = algebraMap (S' ⊗[S] S') R'' (s ⊗ₜ 1) * ϑ₂ r := by
    intro s r; simp [hβ₂def, Algebra.TensorProduct.lift_tmul]

  obtain ⟨hφlin, hφdeg, hφeq⟩ :=
    Algebra.TensorProduct.descent_datum_trans_symm_of_apply_tmul S' R' 𝓡' R'' 𝓡'' ϑ₁ ϑ₂ hϑ₁lin hϑ₂lin
      hϑ₁deg hspan₂ β₁ hβ₁ β₂ hβ₂
  have hφcoc :=
    AlgebraicGeometry.GradedOAlgebra.IsSectionRing.cocycle_trans_symm_of_cocycle S' X' f' L' hL' hva' X'' f'' a₁ a₂
      ha₁ ha₂ X''' f''' b₁₂ b₁₃ b₂₃ hb₁₂ hb₁₃ hb₂₃ h₁ h₂ h₃ ψ hψ R' 𝓡' ι' hR' R'' 𝓡'' ι'' hR'' ϑ₁ ϑ₂ hϑ₁deg hϑ₂deg
      hϑ₁ hϑ₂ hϑ₁lin hϑ₂lin β₁ hβ₁ β₂ hβ₂

  obtain ⟨hbijA, hhomA⟩ :=
    Algebra.bijective_tensorProduct_equalizer_of_faithfullyFlat_of_cocycle S' R' 𝓡' (β₁.trans β₂.symm) hφlin hφdeg hφcoc
  set A : Subalgebra S R' :=
    AlgHom.equalizer ((β₁.trans β₂.symm).toAlgHom.comp (Algebra.TensorProduct.includeLeft : R' →ₐ[S] R' ⊗[S] S'))
      (Algebra.TensorProduct.includeRight : R' →ₐ[S] S' ⊗[S] R') with hAdef
  obtain ⟨𝓐, _, h𝓐, -, hbcA, hirrA⟩ :=
    Subalgebra.exists_gradedAlgebra_isBaseChange_of_bijective_of_decompose_mem S' R' 𝓡' A hbijA hhomA

  have hc₀ := AlgebraicGeometry.GradedOAlgebra.isPullback_projMap_of_isBaseChange S' A 𝓐 R' 𝓡' A.val h𝓐 hbcA hirrA

  obtain ⟨θ', hθ'⟩ := AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_isCanonicalToProj f' L' R' 𝓡' ι' hR' hL' hva'
  haveI : IsIso θ' := AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.isIso f' L' R' 𝓡' ι' hR' hL' hva' θ' hθ'
  have hva'' : Scheme.Modules.ClosedImmersionBySections ((Scheme.Modules.pullback a₁).obj L') f'' := by
    obtain ⟨𝔓'', -, -, hsq⟩ := AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback ha₁' 𝔓
    exact ⟨N, 𝔓'', MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq h𝔓⟩
  obtain ⟨θ'', hθ''⟩ :=
    AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_isCanonicalToProj f'' _ R'' 𝓡'' ι'' hR'' hL'' hva''

  have hirr₁ := HomogeneousIdeal.irrelevant_le_map_of_forall_le_span_image R' 𝓡' R'' 𝓡'' ϑ₁.toRingHom hϑ₁deg
    (fun n _ => hspan₁ n)
  have hirr₂ := HomogeneousIdeal.irrelevant_le_map_of_forall_le_span_image R' 𝓡' R'' 𝓡'' ϑ₂.toRingHom hϑ₂deg
    (fun n _ => hspan₂ n)
  have hnat₁ : θ'' ≫ Proj.map ({ ϑ₁.toRingHom with map_mem := fun h => hϑ₁deg _ _ h } : 𝓡' →+*ᵍ 𝓡'') hirr₁ = a₁ ≫ θ' := by
    letI : Algebra S' R'' := ((algebraMap (S' ⊗[S] S') R'').comp (algebraMap S' (S' ⊗[S] S'))).toAlgebra
    haveI : IsScalarTower S' (S' ⊗[S] S') R'' :=
      IsScalarTower.of_algebraMap_eq (R := S') (S := S' ⊗[S] S') (A := R'') (fun _ => rfl)
    let ϑ₁' : R' →ₐ[S'] R'' :=
      { toRingHom := ϑ₁.toRingHom
        commutes' := fun s => by
          change ϑ₁ (algebraMap S' R' s) = algebraMap (S' ⊗[S] S') R'' (algebraMap S' (S' ⊗[S] S') s)
          rw [Algebra.algebraMap_eq_smul_one, hϑ₁lin, map_one, mul_one]; rfl }
    exact AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.comp_map_eq_comp (S' ⊗[S] S') f' f'' a₁ ha₁' L' hL' _
      (Iso.refl _) R' 𝓡' ι' hR' R'' 𝓡'' ι'' hR'' ϑ₁' hϑ₁deg hϑ₁ hirr₁ θ' hθ' θ'' hθ''
  have hnat₂ : θ'' ≫ Proj.map ({ ϑ₂.toRingHom with map_mem := fun h => hϑ₂deg _ _ h } : 𝓡' →+*ᵍ 𝓡'') hirr₂ = a₂ ≫ θ' := by
    letI instR : Algebra S' (S' ⊗[S] S') := Algebra.TensorProduct.rightAlgebra
    letI : Algebra S' R'' :=
      ((algebraMap (S' ⊗[S] S') R'').comp (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom).toAlgebra

    haveI hst := IsScalarTower.of_algebraMap_eq (R := S') (S := S' ⊗[S] S') (A := R'') (fun _ => rfl)
    let ϑ₂' : R' →ₐ[S'] R'' :=
      { toRingHom := ϑ₂.toRingHom
        commutes' := fun s => by
          change ϑ₂ (algebraMap S' R' s) = algebraMap (S' ⊗[S] S') R'' ((1 : S') ⊗ₜ s)
          rw [Algebra.algebraMap_eq_smul_one, hϑ₂lin, map_one, mul_one] }
    exact AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.comp_map_eq_comp (S' ⊗[S] S') f' f'' a₂ ha₂ L' hL' _
      ψ.symm R' 𝓡' ι' hR' R'' 𝓡'' ι'' hR'' ϑ₂' hϑ₂deg hϑ₂ hirr₂ θ' hθ' θ'' hθ''

  have map_congr : ∀ (g₁ g₂ : 𝓐 →+*ᵍ 𝓡'') (_ : g₁ = g₂)
      (p₁ : HomogeneousIdeal.irrelevant 𝓡'' ≤ (HomogeneousIdeal.irrelevant 𝓐).map g₁)
      (p₂ : HomogeneousIdeal.irrelevant 𝓡'' ≤ (HomogeneousIdeal.irrelevant 𝓐).map g₂), Proj.map g₁ p₁ = Proj.map g₂ p₂ := by
    rintro g₁ _ rfl _ _; rfl
  have hca : a₁ ≫ θ' ≫ Proj.map ({ A.val.toRingHom with map_mem := fun h => h𝓐 _ _ h } : 𝓐 →+*ᵍ 𝓡') hirrA =
      a₂ ≫ θ' ≫ Proj.map ({ A.val.toRingHom with map_mem := fun h => h𝓐 _ _ h } : 𝓐 →+*ᵍ 𝓡') hirrA := by
    rw [← Category.assoc, ← hnat₁, ← Category.assoc a₂, ← hnat₂, Category.assoc, Category.assoc, ← Proj.map_comp,
      ← Proj.map_comp]
    congr 1
    refine map_congr _ _ ?_ _ _
    ext x
    change ϑ₁ (x : R') = ϑ₂ (x : R')
    exact (hφeq x).mp x.2
  have hsq : IsPullback θ' f'
      (Proj.toSpecZero 𝓡' ≫ Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom' 𝓡').comp (algebraMap S' R'))))
      (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact hθ'.comp_toSpecZero⟩
  have hc := hsq.paste_horiz hc₀
  rw [Category.id_comp] at hc
  refine ⟨Proj 𝓐, _, _, hc, hca, ?_⟩
  exact AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isInvertible_pullback_iso_of_cocycle_of_isPullback S' X' f' L'
    hL' X'' f'' a₁ a₂ ha₁ ha₂ X''' f''' b₁₂ b₁₃ b₂₃ hb₁₂ hb₁₃ hb₂₃ h₁ h₂ h₃ ψ hψ (Proj 𝓐) _ _ hc hca

end S_AlgebraicGeometry_exists_descent_of_faithfullyFlat_of_cocycle
end P2MW
export P2MW.S_AlgebraicGeometry_exists_descent_of_faithfullyFlat_of_cocycle (solution)
