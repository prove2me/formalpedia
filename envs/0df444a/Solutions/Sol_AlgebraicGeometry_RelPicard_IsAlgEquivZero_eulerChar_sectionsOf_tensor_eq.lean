-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/f9a53e0a-3fc0-5fa5-b07d-98f2b9ba8075

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_TwoChartCech_isLocallyConstant_fibreEulerChar
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_GeometricallyIntegral_isIntegral_of_flat_of_universallyOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_eulerChar_sectionsOf_tensor_eq
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

open scoped TensorProduct

namespace ChiConst

section Conj

variable {R : Type*} [CommRing R] {M N M' N' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']

noncomputable def kerEquivOfConj (f : M →ₗ[R] N) (f' : M' →ₗ[R] N') (eM : M ≃ₗ[R] M') (eN : N ≃ₗ[R] N')
    (h : ∀ x, eN (f x) = f' (eM x)) : LinearMap.ker f ≃ₗ[R] LinearMap.ker f' :=
  LinearEquiv.ofSubmodules eM (LinearMap.ker f) (LinearMap.ker f') (by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_ker]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [LinearEquiv.coe_coe, ← h, hx, map_zero]
    · intro hy
      refine ⟨eM.symm y, ?_, by simp⟩
      apply eN.injective
      rw [h, LinearEquiv.apply_symm_apply, hy, map_zero])

noncomputable def cokerEquivOfConj (f : M →ₗ[R] N) (f' : M' →ₗ[R] N') (eM : M ≃ₗ[R] M') (eN : N ≃ₗ[R] N')
    (h : ∀ x, eN (f x) = f' (eM x)) : (N ⧸ LinearMap.range f) ≃ₗ[R] (N' ⧸ LinearMap.range f') :=
  Submodule.Quotient.equiv (LinearMap.range f) (LinearMap.range f') eN (by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨eM x, (h x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨f (eM.symm x), ⟨_, rfl⟩, by rw [LinearEquiv.coe_coe, h, LinearEquiv.apply_symm_apply]⟩)

end Conj

section Coker

variable {R : Type*} [CommRing R] {C0 C1 : Type*} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]

theorem nonempty_cokerBaseChangeEquiv (d : C0 →ₗ[R] C1) (A : Type*) [CommRing A] [Algebra R A] :
    Nonempty (((A ⊗[R] C1) ⧸ LinearMap.range (d.baseChange A)) ≃ₗ[A] A ⊗[R] (C1 ⧸ LinearMap.range d)) := by
  let q : C1 →ₗ[R] C1 ⧸ LinearMap.range d := (LinearMap.range d).mkQ
  let qA : A ⊗[R] C1 →ₗ[A] A ⊗[R] (C1 ⧸ LinearMap.range d) := q.baseChange A
  have hsurj : Function.Surjective qA := by
    rw [show (qA : A ⊗[R] C1 → A ⊗[R] (C1 ⧸ LinearMap.range d)) = LinearMap.lTensor A q from
      LinearMap.baseChange_eq_ltensor q]
    exact LinearMap.lTensor_surjective A (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker qA = LinearMap.range (d.baseChange A) := by
    have h1 : LinearMap.ker (LinearMap.lTensor A q) = LinearMap.range (LinearMap.lTensor A d) := by
      rw [lTensor_mkQ]
      have hd : d = (LinearMap.range d).subtype ∘ₗ d.rangeRestrict := LinearMap.ext fun _ => rfl
      conv_rhs => rw [hd, LinearMap.lTensor_comp]
      rw [LinearMap.range_comp_of_range_eq_top]
      exact LinearMap.range_eq_top.mpr (LinearMap.lTensor_surjective A (LinearMap.surjective_rangeRestrict d))
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    have hx : qA x = LinearMap.lTensor A q x := congrFun (LinearMap.baseChange_eq_ltensor q) x
    rw [hx, ← LinearMap.mem_ker, h1, LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, (congrFun (LinearMap.baseChange_eq_ltensor d) y)⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, (congrFun (LinearMap.baseChange_eq_ltensor d) y).symm⟩
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (qA.quotKerEquivOfSurjective hsurj)⟩

end Coker

section FieldExt

variable {R : Type*} [CommRing R] {C0 C1 : Type*} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]

theorem nonempty_kerBaseChangeEquiv_of_flat {K : Type*} [CommRing K] {V0 V1 : Type*} [AddCommGroup V0] [Module K V0]
    [AddCommGroup V1] [Module K V1] (δ : V0 →ₗ[K] V1) (K' : Type*) [CommRing K'] [Algebra K K'] [Module.Flat K K'] :
    Nonempty (LinearMap.ker (δ.baseChange K') ≃ₗ[K'] K' ⊗[K] LinearMap.ker δ) := by
  let ι : K' ⊗[K] LinearMap.ker δ →ₗ[K'] K' ⊗[K] V0 := (LinearMap.ker δ).subtype.baseChange K'
  have hι : ∀ x, δ.baseChange K' (ι x) = 0 := by
    intro x
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.comp_ker_subtype, LinearMap.baseChange_zero,
      LinearMap.zero_apply]
  let j : K' ⊗[K] LinearMap.ker δ →ₗ[K'] LinearMap.ker (δ.baseChange K') := ι.codRestrict _ hι
  have hinj : Function.Injective j := by
    intro x y hxy
    have : ι x = ι y := congrArg Subtype.val hxy
    have hιinj : Function.Injective ι := by
      rw [show (ι : K' ⊗[K] LinearMap.ker δ → K' ⊗[K] V0) = LinearMap.lTensor K' (LinearMap.ker δ).subtype from
        LinearMap.baseChange_eq_ltensor _]
      exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    exact hιinj this
  have hsurj : Function.Surjective j := by
    rintro ⟨x, hx⟩
    have hex : Function.Exact (LinearMap.lTensor K' (LinearMap.ker δ).subtype) (LinearMap.lTensor K' δ) :=
      Module.Flat.lTensor_exact K' (LinearMap.exact_subtype_ker_map δ)
    have hx' : LinearMap.lTensor K' δ x = 0 := by
      rw [← congrFun (LinearMap.baseChange_eq_ltensor δ) x]; exact hx
    obtain ⟨y, hy⟩ := (hex x).mp hx'
    refine ⟨y, Subtype.ext ?_⟩
    change ι y = x
    rw [← hy]
    exact congrFun (LinearMap.baseChange_eq_ltensor _) y
  exact ⟨(LinearEquiv.ofBijective j ⟨hinj, hsurj⟩).symm⟩

theorem baseChange_baseChange_conj (d : C0 →ₗ[R] C1) (K K' : Type*) [CommRing K] [CommRing K'] [Algebra R K]
    [Algebra R K'] [Algebra K K'] [IsScalarTower R K K'] (x : K' ⊗[K] (K ⊗[R] C0)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange R K K' K' C1 ((d.baseChange K).baseChange K' x) =
      d.baseChange K' (TensorProduct.AlgebraTensorModule.cancelBaseChange R K K' K' C0 x) := by
  rw [LinearMap.baseChange_baseChange]
  simp

theorem finrank_ker_coker_baseChange_field {K : Type*} [Field K] {V0 V1 : Type*} [AddCommGroup V0] [Module K V0]
    [AddCommGroup V1] [Module K V1] (δ : V0 →ₗ[K] V1) (K' : Type*) [Field K'] [Algebra K K'] :
    Module.finrank K' (LinearMap.ker (δ.baseChange K')) = Module.finrank K (LinearMap.ker δ) ∧
    Module.finrank K' ((K' ⊗[K] V1) ⧸ LinearMap.range (δ.baseChange K')) =
      Module.finrank K (V1 ⧸ LinearMap.range δ) := by
  obtain ⟨eker⟩ := nonempty_kerBaseChangeEquiv_of_flat δ K'
  obtain ⟨ecok⟩ := nonempty_cokerBaseChangeEquiv δ K'
  exact ⟨eker.finrank_eq.trans Module.finrank_baseChange, ecok.finrank_eq.trans Module.finrank_baseChange⟩

theorem finrank_ker_coker_baseChange_eq (d : C0 →ₗ[R] C1) (K K' : Type*) [Field K] [Field K'] [Algebra R K]
    [Algebra R K'] [Algebra K K'] [IsScalarTower R K K'] :
    Module.finrank K' (LinearMap.ker (d.baseChange K')) = Module.finrank K (LinearMap.ker (d.baseChange K)) ∧
    Module.finrank K' ((K' ⊗[R] C1) ⧸ LinearMap.range (d.baseChange K')) =
      Module.finrank K ((K ⊗[R] C1) ⧸ LinearMap.range (d.baseChange K)) := by
  have hconj := baseChange_baseChange_conj d K K'
  let eK : LinearMap.ker ((d.baseChange K).baseChange K') ≃ₗ[K'] LinearMap.ker (d.baseChange K') :=
    kerEquivOfConj _ _ (TensorProduct.AlgebraTensorModule.cancelBaseChange R K K' K' C0)
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R K K' K' C1) hconj
  let eC : ((K' ⊗[K] (K ⊗[R] C1)) ⧸ LinearMap.range ((d.baseChange K).baseChange K')) ≃ₗ[K']
      ((K' ⊗[R] C1) ⧸ LinearMap.range (d.baseChange K')) :=
    cokerEquivOfConj _ _ (TensorProduct.AlgebraTensorModule.cancelBaseChange R K K' K' C0)
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R K K' K' C1) hconj
  obtain ⟨hk, hc⟩ := finrank_ker_coker_baseChange_field (d.baseChange K) K'
  exact ⟨eK.finrank_eq.symm.trans hk, eC.finrank_eq.symm.trans hc⟩

end FieldExt

section FlatProd

theorem flat_prod {R : Type*} [CommRing R] (M N : Type*) [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [Module.Flat R M] [Module.Flat R N] : Module.Flat R (M × N) := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  have hM := (Module.Flat.iff_lTensor_injective'.mp (inferInstance : Module.Flat R M)) I
  have hN := (Module.Flat.iff_lTensor_injective'.mp (inferInstance : Module.Flat R N)) I
  have key' : ∀ (p : M × N) (i : I), TensorProduct.prodLeft R R M N R (LinearMap.lTensor (M × N) I.subtype (p ⊗ₜ i)) =
      ((LinearMap.lTensor M I.subtype).prodMap (LinearMap.lTensor N I.subtype)) (TensorProduct.prodLeft R R M N I (p ⊗ₜ i)) := by
    intro p i
    obtain ⟨m, n⟩ := p
    simp [TensorProduct.prodLeft_tmul, LinearMap.lTensor_tmul]
  have key : ∀ x, TensorProduct.prodLeft R R M N R (LinearMap.lTensor (M × N) I.subtype x) =
      ((LinearMap.lTensor M I.subtype).prodMap (LinearMap.lTensor N I.subtype)) (TensorProduct.prodLeft R R M N I x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul p i => exact key' p i
  intro x y hxy
  apply (TensorProduct.prodLeft R R M N I).injective
  have hxy' := congrArg (TensorProduct.prodLeft R R M N R) hxy
  rw [key, key] at hxy'
  have h1 := congrArg Prod.fst hxy'
  have h2 := congrArg Prod.snd hxy'
  simp only [LinearMap.prodMap_apply] at h1 h2
  exact Prod.ext (hM h1) (hN h2)

end FlatProd

end ChiConst

namespace ChiConst

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v w v' w'

theorem nonempty_H0_H1_equiv_of_equiv {R : Type u} [CommRing R] {𝒰 : TwoChartCech.Cover.{u, v} R}
    {𝒰' : TwoChartCech.Cover.{u, v'} R} (S : TwoChartCech.Sections.{u, v, w} 𝒰) (S' : TwoChartCech.Sections.{u, v', w'} 𝒰')
    (e0 : S.M0 ≃ₗ[R] S'.M0) (e1 : S.M1 ≃ₗ[R] S'.M1) (e01 : S.M01 ≃ₗ[R] S'.M01)
    (h0 : ∀ x, e01 (S.r0 x) = S'.r0 (e0 x)) (h1 : ∀ x, e01 (S.r1 x) = S'.r1 (e1 x)) :
    Nonempty (S.H0 ≃ₗ[R] S'.H0) ∧ Nonempty (S.H1 ≃ₗ[R] S'.H1) := by
  have hconj : ∀ x, e01 (S.cechDiff x) = S'.cechDiff (e0.prodCongr e1 x) := by
    intro x
    rw [TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Sections.cechDiff_apply, map_sub, h0, h1]
    rfl
  exact ⟨⟨kerEquivOfConj _ _ _ _ hconj⟩, ⟨cokerEquivOfConj _ _ _ _ hconj⟩⟩

section Transport

variable {X X' : Scheme.{u}} (φ : X' ⟶ X) [IsIso φ]

noncomputable def pushforwardEquivOfIsIso : X'.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pushforward φ) (Scheme.Modules.pushforward (inv φ))
    ((Scheme.Modules.pushforwardId X').symm ≪≫ Scheme.Modules.pushforwardCongr (IsIso.hom_inv_id φ).symm ≪≫
      (Scheme.Modules.pushforwardComp φ (inv φ)).symm)
    (Scheme.Modules.pushforwardComp (inv φ) φ ≪≫ Scheme.Modules.pushforwardCongr (IsIso.inv_hom_id φ) ≪≫
      Scheme.Modules.pushforwardId X)

noncomputable def pullbackIsoPushforwardInv : Scheme.Modules.pullback φ ≅ Scheme.Modules.pushforward (inv φ) :=
  Adjunction.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction φ)
    (pushforwardEquivOfIsIso φ).symm.toAdjunction

noncomputable def pushforwardIsoOfIsoPullback (G : X.Modules) (G' : X'.Modules)
    (e : G' ≅ (Scheme.Modules.pullback φ).obj G) : (Scheme.Modules.pushforward φ).obj G' ≅ G :=
  (Scheme.Modules.pushforward φ).mapIso (e ≪≫ (pullbackIsoPushforwardInv φ).app G) ≪≫
    (pushforwardEquivOfIsIso φ).counitIso.app G

variable {R : Type u} [CommRing R] (c : X ⟶ Spec (.of R))

omit [IsIso φ] in
theorem appLE_comp_eq_app_appLE (U : X.Opens) :
    (φ ≫ c).appLE ⊤ (φ ⁻¹ᵁ U) le_top = c.appLE ⊤ U le_top ≫ φ.app U := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]

omit [IsIso φ] in
theorem algebraMap_comp_apply (U : X.Opens) (r : R) :
    (Scheme.TwoAffineOpenCover.algebraOfHom (φ ≫ c) (φ ⁻¹ᵁ U)).algebraMap r =
      (φ.app U).hom ((Scheme.TwoAffineOpenCover.algebraOfHom c U).algebraMap r) := by
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom, Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom,
    appLE_comp_eq_app_appLE, CommRingCat.comp_apply]

noncomputable def evalIso (G : X.Modules) (G' : X'.Modules) (ι : (Scheme.Modules.pushforward φ).obj G' ≅ G)
    (U : X.Opens) : ((Scheme.Modules.pushforward φ).obj G').val.obj (op U) ≅ G.val.obj (op U) :=
  (SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (op U)).mapIso ι

noncomputable def sectionsEquiv (G : X.Modules) (G' : X'.Modules) (ι : (Scheme.Modules.pushforward φ).obj G' ≅ G)
    (U : X.Opens) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (φ ≫ c) G' (φ ⁻¹ᵁ U)
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c G U
    Γ(G', φ ⁻¹ᵁ U) ≃ₗ[R] Γ(G, U) :=
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (φ ≫ c) G' (φ ⁻¹ᵁ U)
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c G U
  { toFun := fun m => (evalIso φ G G' ι U).toLinearEquiv m
    invFun := fun n => (evalIso φ G G' ι U).toLinearEquiv.symm n
    map_add' := fun x y => map_add _ x y
    map_smul' := fun r m => by
      letI := Scheme.TwoAffineOpenCover.algebraOfHom (φ ≫ c) (φ ⁻¹ᵁ U)
      letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
      change (evalIso φ G G' ι U).toLinearEquiv ((algebraMap R Γ(X', φ ⁻¹ᵁ U) r) • m) =
        (algebraMap R Γ(X, U) r) • (evalIso φ G G' ι U).toLinearEquiv m
      rw [show algebraMap R Γ(X', φ ⁻¹ᵁ U) r = (φ.app U).hom (algebraMap R Γ(X, U) r) from
        algebraMap_comp_apply φ c U r]
      exact (evalIso φ G G' ι U).toLinearEquiv.map_smul (algebraMap R Γ(X, U) r) m
    left_inv := fun m => (evalIso φ G G' ι U).toLinearEquiv.left_inv m
    right_inv := fun n => (evalIso φ G G' ι U).toLinearEquiv.right_inv n }

omit [IsIso φ] in
theorem sectionsEquiv_apply (G : X.Modules) (G' : X'.Modules) (ι : (Scheme.Modules.pushforward φ).obj G' ≅ G)
    (U : X.Opens) (m : Γ(G', φ ⁻¹ᵁ U)) :
    sectionsEquiv φ c G G' ι U m = (ι.hom.val.app (op U)).hom m := rfl

omit [IsIso φ] in

theorem sectionsEquiv_map (G : X.Modules) (G' : X'.Modules) (ι : (Scheme.Modules.pushforward φ).obj G' ≅ G)
    {U V : X.Opens} (h : V ≤ U) (m : Γ(G', φ ⁻¹ᵁ U)) :
    sectionsEquiv φ c G G' ι V ((G'.val.map (homOfLE (show φ ⁻¹ᵁ V ≤ φ ⁻¹ᵁ U from fun _ hx => h hx)).op).hom m) =
      (G.val.map (homOfLE h).op).hom (sectionsEquiv φ c G G' ι U m) := by
  rw [sectionsEquiv_apply, sectionsEquiv_apply]
  exact PresheafOfModules.naturality_apply ι.hom.val (homOfLE h).op m

theorem nonempty_H0_H1_equiv_of_isIso {R : Type u} [CommRing R] {X X' : Scheme.{u}} (φ : X' ⟶ X) [IsIso φ]
    (c : X ⟶ Spec (.of R)) (c' : X' ⟶ Spec (.of R)) (hc : c' = φ ≫ c)
    (𝒱 : X.TwoAffineOpenCover) (𝒱' : X'.TwoAffineOpenCover) (h0 : 𝒱'.U0 = φ ⁻¹ᵁ 𝒱.U0) (h1 : 𝒱'.U1 = φ ⁻¹ᵁ 𝒱.U1)
    (G : X.Modules) (G' : X'.Modules) (e : G' ≅ (Scheme.Modules.pullback φ).obj G) :
    Nonempty ((𝒱'.sectionsOf c' G').H0 ≃ₗ[R] (𝒱.sectionsOf c G).H0) ∧
      Nonempty ((𝒱'.sectionsOf c' G').H1 ≃ₗ[R] (𝒱.sectionsOf c G).H1) := by
  subst hc
  obtain ⟨U0', U1', hU0', hU1', hsup', hinf'⟩ := 𝒱'
  simp only at h0 h1
  subst h0
  subst h1
  let ι := pushforwardIsoOfIsoPullback φ G G' e
  refine nonempty_H0_H1_equiv_of_equiv _ _ (sectionsEquiv φ c G G' ι 𝒱.U0) (sectionsEquiv φ c G G' ι 𝒱.U1)
    (sectionsEquiv φ c G G' ι (𝒱.U0 ⊓ 𝒱.U1)) ?_ ?_
  · intro x
    exact sectionsEquiv_map φ c G G' ι inf_le_left x
  · intro x
    exact sectionsEquiv_map φ c G G' ι inf_le_right x

end Transport

end ChiConst

namespace ChiConst

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra Opposite CategoryTheory.MonoidalCategory"

open scoped TensorProduct

universe u

section Fibre

variable {k : Type u} [Field k] {A : Scheme.{u}} (a : A ⟶ Spec (.of k)) (𝒱 : A.TwoAffineOpenCover)
  {T' : Scheme.{u}} (h : T' ⟶ Spec (.of k)) (F : (pullback a h).Modules) (hF : Scheme.Modules.IsInvertible F)

theorem specMap_comp_specMap (B K : Type u) [CommRing B] [CommRing K] [Algebra k B] [Algebra k K] [Algebra B K]
    [IsScalarTower k B K] :
    Scheme.TwoAffineOpenCover.specMap B K ≫ Scheme.TwoAffineOpenCover.specMap k B = Scheme.TwoAffineOpenCover.specMap k K := by
  rw [Scheme.TwoAffineOpenCover.specMap, Scheme.TwoAffineOpenCover.specMap, Scheme.TwoAffineOpenCover.specMap,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

theorem congrHom_hom_fst {X Y Z : Scheme.{u}} (f : X ⟶ Z) {g g' : Y ⟶ Z} (hg : g = g') :
    (pullback.congrHom (rfl : f = f) hg).hom ≫ pullback.fst f g' = pullback.fst f g := by
  subst hg; simp

theorem congrHom_hom_snd {X Y Z : Scheme.{u}} (f : X ⟶ Z) {g g' : Y ⟶ Z} (hg : g = g') :
    (pullback.congrHom (rfl : f = f) hg).hom ≫ pullback.snd f g' = pullback.snd f g := by
  subst hg; simp

include hF in

theorem fibreEulerChar_eq_finrank_sub (B : Type u) [CommRing B] [Algebra k B]
    (sB : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap k B) h)
    (K : Type u) [Field K] [Algebra k K] [Algebra B K] [IsScalarTower k B K]
    (sK : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap k K) h)
    (hsK : sK.1 = Scheme.TwoAffineOpenCover.specMap B K ≫ sB.1)
    (𝔮 : PrimeSpectrum B) (h𝔮 : 𝔮.asIdeal = RingHom.ker (algebraMap B K)) :
    ((Module.finrank 𝔮.asIdeal.ResidueField (LinearMap.ker (((𝒱.pullback a B).sectionsOf (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B)) ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F)).cechDiff.baseChange 𝔮.asIdeal.ResidueField)) : ℤ) - Module.finrank 𝔮.asIdeal.ResidueField ((𝔮.asIdeal.ResidueField ⊗[B] ((𝒱.pullback a B).sectionsOf (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B)) ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F)).M01) ⧸ LinearMap.range (((𝒱.pullback a B).sectionsOf (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B)) ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F)).cechDiff.baseChange 𝔮.asIdeal.ResidueField))) =
    ((Module.finrank K ((𝒱.pullback a K).sectionsOf (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k K)) ((Scheme.Modules.pullback (baseChangeSnd a sK)).obj F)).H0 : ℤ) - Module.finrank K ((𝒱.pullback a K).sectionsOf (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k K)) ((Scheme.Modules.pullback (baseChangeSnd a sK)).obj F)).H1) := by

  have hle : 𝔮.asIdeal ≤ RingHom.ker (algebraMap B K) := h𝔮.le
  have hunit : 𝔮.asIdeal.primeCompl ≤ Submonoid.comap (algebraMap B K) (IsUnit.submonoid K) := by
    intro x hx
    rw [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    intro h0
    exact hx (h𝔮 ▸ (RingHom.mem_ker.mpr h0))
  letI : Algebra 𝔮.asIdeal.ResidueField K := (Ideal.ResidueField.lift 𝔮.asIdeal (algebraMap B K) hle hunit).toAlgebra
  haveI : IsScalarTower B 𝔮.asIdeal.ResidueField K := IsScalarTower.of_algebraMap_eq fun b =>
    (Ideal.ResidueField.lift_algebraMap 𝔮.asIdeal (algebraMap B K) hle hunit b).symm
  obtain ⟨hker, hcoker⟩ := finrank_ker_coker_baseChange_eq ((𝒱.pullback a B).sectionsOf (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B)) ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F)).cechDiff 𝔮.asIdeal.ResidueField K
  rw [← hker, ← hcoker]

  have hFB : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F) := hF.pullback _
  obtain ⟨⟨eH1⟩, ⟨eH0⟩, -⟩ :=
    Scheme.TwoAffineOpenCover.exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial (𝒱.pullback a B)
      (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B)) ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F) hFB.1 K
  obtain ⟨ecok⟩ := nonempty_cokerBaseChangeEquiv ((𝒱.pullback a B).sectionsOf (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B)) ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F)).cechDiff K
  rw [← eH0.finrank_eq, ecok.finrank_eq, ← eH1.finrank_eq]

  have hg : Scheme.TwoAffineOpenCover.specMap B K ≫ Scheme.TwoAffineOpenCover.specMap k B = Scheme.TwoAffineOpenCover.specMap k K := specMap_comp_specMap B K
  let ψ : pullback (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B)) (Scheme.TwoAffineOpenCover.specMap B K) ≅ pullback a (Scheme.TwoAffineOpenCover.specMap k K) :=
    pullbackLeftPullbackSndIso a (Scheme.TwoAffineOpenCover.specMap k B) (Scheme.TwoAffineOpenCover.specMap B K) ≪≫ pullback.congrHom rfl hg
  have hψfst : ψ.hom ≫ pullback.fst a (Scheme.TwoAffineOpenCover.specMap k K) =
      pullback.fst (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B)) (Scheme.TwoAffineOpenCover.specMap B K) ≫ pullback.fst a (Scheme.TwoAffineOpenCover.specMap k B) := by
    simp only [ψ, Iso.trans_hom, Category.assoc, congrHom_hom_fst, pullbackLeftPullbackSndIso_hom_fst]
  have hψsnd : ψ.hom ≫ pullback.snd a (Scheme.TwoAffineOpenCover.specMap k K) =
      pullback.snd (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B)) (Scheme.TwoAffineOpenCover.specMap B K) := by
    simp only [ψ, Iso.trans_hom, Category.assoc, congrHom_hom_snd, pullbackLeftPullbackSndIso_hom_snd]
  let φ := ψ.inv
  have hφfst : φ ≫ pullback.fst (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B)) (Scheme.TwoAffineOpenCover.specMap B K) ≫
      pullback.fst a (Scheme.TwoAffineOpenCover.specMap k B) = pullback.fst a (Scheme.TwoAffineOpenCover.specMap k K) := by
    rw [← hψfst, Iso.inv_hom_id_assoc]
  have hφsnd : φ ≫ pullback.snd (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B)) (Scheme.TwoAffineOpenCover.specMap B K) =
      pullback.snd a (Scheme.TwoAffineOpenCover.specMap k K) := by
    rw [← hψsnd, Iso.inv_hom_id_assoc]
  have h0 : (𝒱.pullback a K).U0 = φ ⁻¹ᵁ ((𝒱.pullback a B).pullback (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B)) K).U0 := by
    change pullback.fst a (Scheme.TwoAffineOpenCover.specMap k K) ⁻¹ᵁ 𝒱.U0 =
      φ ⁻¹ᵁ (pullback.fst (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B)) (Scheme.TwoAffineOpenCover.specMap B K) ⁻¹ᵁ
        (pullback.fst a (Scheme.TwoAffineOpenCover.specMap k B) ⁻¹ᵁ 𝒱.U0))
    rw [← hφfst]
    rfl
  have h1 : (𝒱.pullback a K).U1 = φ ⁻¹ᵁ ((𝒱.pullback a B).pullback (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B)) K).U1 := by
    change pullback.fst a (Scheme.TwoAffineOpenCover.specMap k K) ⁻¹ᵁ 𝒱.U1 =
      φ ⁻¹ᵁ (pullback.fst (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B)) (Scheme.TwoAffineOpenCover.specMap B K) ⁻¹ᵁ
        (pullback.fst a (Scheme.TwoAffineOpenCover.specMap k B) ⁻¹ᵁ 𝒱.U1))
    rw [← hφfst]
    rfl
  have hmap : (φ ≫ pullback.fst (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B)) (Scheme.TwoAffineOpenCover.specMap B K)) ≫ baseChangeSnd a sB =
      baseChangeSnd a sK := by
    apply pullback.hom_ext
    · unfold baseChangeSnd
      simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
      exact hφfst
    · unfold baseChangeSnd
      simp only [Category.assoc, pullback.lift_snd]
      rw [hsK, pullback.condition_assoc, ← Category.assoc φ, hφsnd]
  let e : (Scheme.Modules.pullback (baseChangeSnd a sK)).obj F ≅ (Scheme.Modules.pullback φ).obj
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B)) (Scheme.TwoAffineOpenCover.specMap B K))).obj
        ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F)) :=
    ((Scheme.Modules.pullbackCongr hmap).app F).symm ≪≫
      ((Scheme.Modules.pullbackComp (φ ≫ pullback.fst (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B)) (Scheme.TwoAffineOpenCover.specMap B K))
        (baseChangeSnd a sB)).app F).symm ≪≫
      ((Scheme.Modules.pullbackComp φ (pullback.fst (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B)) (Scheme.TwoAffineOpenCover.specMap B K))).app _).symm
  obtain ⟨⟨f0⟩, ⟨f1⟩⟩ := nonempty_H0_H1_equiv_of_isIso φ
    (pullback.snd (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B)) (Scheme.TwoAffineOpenCover.specMap B K)) (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k K)) hφsnd.symm
    ((𝒱.pullback a B).pullback (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k B)) K) (𝒱.pullback a K) h0 h1 _ _ e
  rw [f0.finrank_eq, f1.finrank_eq]

end Fibre

section Charts

variable {k : Type u} [Field k] {A : Scheme.{u}} (a : A ⟶ Spec (.of k)) [IsProper a] (𝒱 : A.TwoAffineOpenCover)
  {T' : Scheme.{u}} (h : T' ⟶ Spec (.of k))
  (F : (pullback a h).Modules) (hF : Scheme.Modules.IsInvertible F)

theorem fromSpec_comp_eq_specMap (W : T'.Opens) (hW : IsAffineOpen W) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom h W
    hW.fromSpec ≫ h = Scheme.TwoAffineOpenCover.specMap k Γ(T', W) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom h W
  have e1 : CommRingCat.ofHom (algebraMap k Γ(T', W)) = (Scheme.ΓSpecIso (.of k)).inv ≫ h.appLE ⊤ W le_top := rfl
  rw [Scheme.TwoAffineOpenCover.specMap, e1, Spec.map_comp, ← Scheme.isoSpec_Spec_inv,
    ← IsAffineOpen.fromSpec_top, IsAffineOpen.SpecMap_appLE_fromSpec h (isAffineOpen_top _) hW]

theorem exists_algebra_of_range_subset (W : T'.Opens) (hW : IsAffineOpen W)
    (K : Type u) [Field K] [Algebra k K] (s : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap k K) h)
    (hs : Set.range ⇑s.1 ⊆ (W : Set T')) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom h W
    ∃ (_ : Algebra Γ(T', W) K) (_ : IsScalarTower k Γ(T', W) K),
      s.1 = Scheme.TwoAffineOpenCover.specMap Γ(T', W) K ≫ hW.fromSpec := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom h W
  haveI := hW.isOpenImmersion_fromSpec
  let τ : Spec (.of K) ⟶ Spec Γ(T', W) := IsOpenImmersion.lift hW.fromSpec s.1 (by
    rw [IsAffineOpen.range_fromSpec]; exact hs)
  have hτ : τ ≫ hW.fromSpec = s.1 := IsOpenImmersion.lift_fac _ _ _
  let θ : Γ(T', W) ⟶ CommRingCat.of K := Spec.preimage τ
  have hθ : Spec.map θ = τ := Spec.map_preimage τ
  letI : Algebra Γ(T', W) K := θ.hom.toAlgebra
  have hspec : Scheme.TwoAffineOpenCover.specMap Γ(T', W) K = τ := by
    rw [← hθ]; rfl
  refine ⟨inferInstance, IsScalarTower.of_algebraMap_eq fun x => ?_, by rw [hspec, hτ]⟩
  have key : CommRingCat.ofHom (algebraMap k K) = CommRingCat.ofHom (algebraMap k Γ(T', W)) ≫ θ := by
    apply Spec.map_injective
    change Scheme.TwoAffineOpenCover.specMap k K = _
    rw [Spec.map_comp, hθ, ← s.2, ← hτ, Category.assoc, fromSpec_comp_eq_specMap h W hW]
  have key' := congrArg CommRingCat.Hom.hom key
  rw [CommRingCat.hom_ofHom, CommRingCat.hom_comp, CommRingCat.hom_ofHom] at key'
  exact RingHom.congr_fun key' x

variable [LocallyOfFiniteType h] [GeometricallyIntegral h]

include hF in

theorem finrank_sub_eq_of_subset (W : T'.Opens) (hW : IsAffineOpen W)
    (K₁ : Type u) [Field K₁] [Algebra k K₁] (s₁ : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap k K₁) h)
    (hs₁ : Set.range ⇑s₁.1 ⊆ (W : Set T'))
    (K₂ : Type u) [Field K₂] [Algebra k K₂] (s₂ : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap k K₂) h)
    (hs₂ : Set.range ⇑s₂.1 ⊆ (W : Set T')) :
    ((Module.finrank K₁ ((𝒱.pullback a K₁).sectionsOf (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k K₁)) ((Scheme.Modules.pullback (baseChangeSnd a s₁)).obj F)).H0 : ℤ) - Module.finrank K₁ ((𝒱.pullback a K₁).sectionsOf (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k K₁)) ((Scheme.Modules.pullback (baseChangeSnd a s₁)).obj F)).H1) =
    ((Module.finrank K₂ ((𝒱.pullback a K₂).sectionsOf (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k K₂)) ((Scheme.Modules.pullback (baseChangeSnd a s₂)).obj F)).H0 : ℤ) - Module.finrank K₂ ((𝒱.pullback a K₂).sectionsOf (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k K₂)) ((Scheme.Modules.pullback (baseChangeSnd a s₂)).obj F)).H1) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom h W

  haveI : Nonempty W := by
    obtain ⟨x⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of K₁)))
    exact ⟨⟨s₁.1.base x, hs₁ ⟨x, rfl⟩⟩⟩
  haveI : IsLocallyNoetherian T' := LocallyOfFiniteType.isLocallyNoetherian h
  haveI : IsNoetherianRing Γ(T', W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  haveI : IsIntegral T' := GeometricallyIntegral.isIntegral_of_flat_of_universallyOpen h
  haveI : IsDomain Γ(T', W) := IsIntegral.component_integral W

  let sB : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap k Γ(T', W)) h := ⟨hW.fromSpec, fromSpec_comp_eq_specMap h W hW⟩
  have hFB : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F) := hF.pullback _

  haveI : Flat (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k Γ(T', W))) := MorphismProperty.pullback_snd (P := @Flat) _ _ inferInstance
  have flatOf : ∀ (U : (pullback a (Scheme.TwoAffineOpenCover.specMap k Γ(T', W))).Opens) (hU : IsAffineOpen U),
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k Γ(T', W)))
        ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F) U
      Module.Flat Γ(T', W) Γ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F, U) := by
    intro U hU
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k Γ(T', W))) U
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k Γ(T', W)))
      ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F) U
    haveI := Scheme.TwoAffineOpenCover.isScalarTower_sections (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k Γ(T', W)))
      ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F) U
    haveI : Module.Flat Γ(T', W) Γ(pullback a (Scheme.TwoAffineOpenCover.specMap k Γ(T', W)), U) :=
      Scheme.TwoAffineOpenCover.flat_sections_of_flat (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k Γ(T', W))) U hU
    haveI : Module.Projective Γ(pullback a (Scheme.TwoAffineOpenCover.specMap k Γ(T', W)), U)
        Γ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F, U) :=
      Scheme.Modules.projective_sections_of_locallyTrivial _ hFB.1 ⟨U, hU⟩
    exact Module.Flat.trans Γ(T', W) Γ(pullback a (Scheme.TwoAffineOpenCover.specMap k Γ(T', W)), U)
      Γ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F, U)
  haveI : Module.Flat Γ(T', W) ((𝒱.pullback a Γ(T', W)).sectionsOf (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k Γ(T', W))) ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F)).M0 := flatOf _ (𝒱.pullback a Γ(T', W)).isAffineOpen_U0
  haveI : Module.Flat Γ(T', W) ((𝒱.pullback a Γ(T', W)).sectionsOf (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k Γ(T', W))) ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F)).M1 := flatOf _ (𝒱.pullback a Γ(T', W)).isAffineOpen_U1
  haveI : Module.Flat Γ(T', W) ((𝒱.pullback a Γ(T', W)).sectionsOf (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k Γ(T', W))) ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F)).M01 := flatOf _ (𝒱.pullback a Γ(T', W)).isAffineOpen_inf
  haveI : Module.Flat Γ(T', W) (((𝒱.pullback a Γ(T', W)).sectionsOf (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k Γ(T', W))) ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F)).M0 × ((𝒱.pullback a Γ(T', W)).sectionsOf (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k Γ(T', W))) ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F)).M1) := flat_prod _ _

  haveI : IsProper (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k Γ(T', W))) :=
    MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  have hcf := OModulePresheaf.cechFinite_ofModules_of_locallyTrivial (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k Γ(T', W)))
    ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F) hFB.1 (𝒱.pullback a Γ(T', W)).toOrderedAffineCover
  obtain ⟨hfin0, hfin1⟩ := (OModulePresheaf.cechFinite_toOrderedAffineCover_iff _ _).mp hcf
  haveI : Module.Finite Γ(T', W) (LinearMap.ker ((𝒱.pullback a Γ(T', W)).sectionsOf (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k Γ(T', W))) ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F)).cechDiff) := hfin0
  haveI : Module.Finite Γ(T', W) (((𝒱.pullback a Γ(T', W)).sectionsOf (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k Γ(T', W))) ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F)).M01 ⧸ LinearMap.range ((𝒱.pullback a Γ(T', W)).sectionsOf (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k Γ(T', W))) ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F)).cechDiff) := hfin1
  have hlc := TwoChartCech.isLocallyConstant_fibreEulerChar ((𝒱.pullback a Γ(T', W)).sectionsOf (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k Γ(T', W))) ((Scheme.Modules.pullback (baseChangeSnd a sB)).obj F)).cechDiff

  obtain ⟨i₁, t₁, hsK₁⟩ := exists_algebra_of_range_subset h W hW K₁ s₁ hs₁
  obtain ⟨i₂, t₂, hsK₂⟩ := exists_algebra_of_range_subset h W hW K₂ s₂ hs₂
  let 𝔮₁ : PrimeSpectrum Γ(T', W) := ⟨RingHom.ker (algebraMap Γ(T', W) K₁), RingHom.ker_isPrime _⟩
  let 𝔮₂ : PrimeSpectrum Γ(T', W) := ⟨RingHom.ker (algebraMap Γ(T', W) K₂), RingHom.ker_isPrime _⟩
  have e₁ := fibreEulerChar_eq_finrank_sub a 𝒱 h F hF Γ(T', W) sB K₁ s₁ hsK₁ 𝔮₁ rfl
  have e₂ := fibreEulerChar_eq_finrank_sub a 𝒱 h F hF Γ(T', W) sB K₂ s₂ hsK₂ 𝔮₂ rfl
  have e₁₂ := hlc.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ 𝔮₁) (Set.mem_univ 𝔮₂)
  exact e₁.symm.trans (e₁₂.trans e₂)

end Charts

section Main

theorem main_aux {k : Type u} [Field k] {A : Scheme.{u}} (a : A ⟶ Spec (.of k)) [IsProper a]
    (𝒱 : A.TwoAffineOpenCover) (L M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    {T' : Scheme.{u}} (h : T' ⟶ Spec (.of k)) [LocallyOfFiniteType h] [GeometricallyIntegral h]
    (N : (pullback a h).Modules) (hN : Scheme.Modules.IsInvertible N)
    (g : Spec (.of k) ⟶ Spec (.of k)) (hg : g = Scheme.TwoAffineOpenCover.specMap k k) (hg1 : g = 𝟙 _) (t₀ t₁ : SchemeHomOver g h)
    (e₀ : Nonempty ((Scheme.Modules.pullback (baseChangeSnd a t₀)).obj N ≅
      SheafOfModules.unit (pullback a g).ringCatSheaf))
    (e₁ : Nonempty ((Scheme.Modules.pullback (baseChangeSnd a t₁)).obj N ≅
      (Scheme.Modules.pullback (pullback.fst a g)).obj L)) :
    (Module.finrank k (𝒱.sectionsOf a (L ⊗ M)).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf a (L ⊗ M)).H1
      = (Module.finrank k (𝒱.sectionsOf a M).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf a M).H1 := by
  subst hg

  have hF : Scheme.Modules.IsInvertible (N ⊗ (Scheme.Modules.pullback (pullback.fst a h)).obj M) :=
    hN.tensor (hM.pullback _)

  haveI : IsIso (Scheme.TwoAffineOpenCover.specMap k k) := by rw [hg1]; infer_instance
  have hcomp : ∀ {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)), f ≫ Scheme.TwoAffineOpenCover.specMap k k = f := fun f => by
    rw [hg1]; exact Category.comp_id f
  have hc : pullback.snd a (Scheme.TwoAffineOpenCover.specMap k k) = pullback.fst a (Scheme.TwoAffineOpenCover.specMap k k) ≫ a := (pullback.condition.trans (hcomp _)).symm
  have hbcs : ∀ t : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap k k) h, baseChangeSnd a t ≫ pullback.fst a h = pullback.fst a (Scheme.TwoAffineOpenCover.specMap k k) := by
    intro t
    unfold baseChangeSnd
    simp only [pullback.lift_fst, Category.comp_id]

  let E₁ : (Scheme.Modules.pullback (baseChangeSnd a t₁)).obj (N ⊗ (Scheme.Modules.pullback (pullback.fst a h)).obj M) ≅
      (Scheme.Modules.pullback (pullback.fst a (Scheme.TwoAffineOpenCover.specMap k k))).obj (L ⊗ M) :=
    Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      (e₁.some ⊗ᵢ ((Scheme.Modules.pullbackComp (baseChangeSnd a t₁) (pullback.fst a h)).app M ≪≫
        (Scheme.Modules.pullbackCongr (hbcs t₁)).app M)) ≪≫
      (Scheme.Modules.pullbackTensorObjIso _ _ _).symm
  let E₀ : (Scheme.Modules.pullback (baseChangeSnd a t₀)).obj (N ⊗ (Scheme.Modules.pullback (pullback.fst a h)).obj M) ≅
      (Scheme.Modules.pullback (pullback.fst a (Scheme.TwoAffineOpenCover.specMap k k))).obj M :=
    Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      (e₀.some ⊗ᵢ ((Scheme.Modules.pullbackComp (baseChangeSnd a t₀) (pullback.fst a h)).app M ≪≫
        (Scheme.Modules.pullbackCongr (hbcs t₀)).app M)) ≪≫
      λ_ _
  obtain ⟨⟨f0₁⟩, ⟨f1₁⟩⟩ := nonempty_H0_H1_equiv_of_isIso (pullback.fst a (Scheme.TwoAffineOpenCover.specMap k k)) a (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k k)) hc
    𝒱 (𝒱.pullback a k) rfl rfl (L ⊗ M) _ E₁
  obtain ⟨⟨f0₀⟩, ⟨f1₀⟩⟩ := nonempty_H0_H1_equiv_of_isIso (pullback.fst a (Scheme.TwoAffineOpenCover.specMap k k)) a (pullback.snd a (Scheme.TwoAffineOpenCover.specMap k k)) hc
    𝒱 (𝒱.pullback a k) rfl rfl M _ E₀
  rw [← f0₁.finrank_eq, ← f1₁.finrank_eq, ← f0₀.finrank_eq, ← f1₀.finrank_eq]

  obtain ⟨W₀, hW₀, hx₀, -⟩ := exists_isAffineOpen_mem_and_subset (x := t₀.1.base default) (U := (⊤ : T'.Opens)) trivial
  obtain ⟨W₁, hW₁, hx₁, -⟩ := exists_isAffineOpen_mem_and_subset (x := t₁.1.base default) (U := (⊤ : T'.Opens)) trivial
  have hr₀ : Set.range ⇑t₀.1 ⊆ (W₀ : Set T') :=
    Set.range_subset_iff.mpr fun y => by rw [Unique.eq_default y]; exact hx₀
  have hr₁ : Set.range ⇑t₁.1 ⊆ (W₁ : Set T') :=
    Set.range_subset_iff.mpr fun y => by rw [Unique.eq_default y]; exact hx₁
  haveI : IsIntegral T' := GeometricallyIntegral.isIntegral_of_flat_of_universallyOpen h
  obtain ⟨y, hy₀, hy₁⟩ := nonempty_preirreducible_inter W₀.isOpen W₁.isOpen ⟨_, hx₀⟩ ⟨_, hx₁⟩

  letI : Algebra k (T'.residueField y) := (Spec.preimage (T'.fromSpecResidueField y ≫ h)).hom.toAlgebra
  have hσ : T'.fromSpecResidueField y ≫ h = Scheme.TwoAffineOpenCover.specMap k (T'.residueField y) := by
    change T'.fromSpecResidueField y ≫ h = Spec.map (CommRingCat.ofHom (Spec.preimage (T'.fromSpecResidueField y ≫ h)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  let sy : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap k (T'.residueField y)) h := ⟨T'.fromSpecResidueField y, hσ⟩
  have hry : Set.range ⇑sy.1 = {y} := Scheme.range_fromSpecResidueField y
  have hy₀' : Set.range ⇑sy.1 ⊆ (W₀ : Set T') := by rw [hry]; exact Set.singleton_subset_iff.mpr hy₀
  have hy₁' : Set.range ⇑sy.1 ⊆ (W₁ : Set T') := by rw [hry]; exact Set.singleton_subset_iff.mpr hy₁
  have c₁ := finrank_sub_eq_of_subset a 𝒱 h _ hF W₁ hW₁ k t₁ hr₁ (T'.residueField y) sy hy₁'
  have c₀ := finrank_sub_eq_of_subset a 𝒱 h _ hF W₀ hW₀ (T'.residueField y) sy hy₀' k t₀ hr₀
  exact c₁.trans c₀

theorem main {k : Type u} [Field k] {A : Scheme.{u}} (a : A ⟶ Spec (.of k)) [IsProper a] (𝒱 : A.TwoAffineOpenCover)
    (L M : A.Modules) (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (h0 : RelPicard.IsAlgEquivZero a L) :
    (Module.finrank k (𝒱.sectionsOf a (L ⊗ M)).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf a (L ⊗ M)).H1
      = (Module.finrank k (𝒱.sectionsOf a M).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf a M).H1 := by
  obtain ⟨T', h, hft, hgi, N, hN, t₀, t₁, e₀, e₁⟩ := h0
  haveI := hft
  haveI := hgi
  have hk : Scheme.TwoAffineOpenCover.specMap k k = 𝟙 (Spec (.of k)) := by
    change Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 _
    rw [CommRingCat.ofHom_id, Spec.map_id]
  exact main_aux a 𝒱 L M hM h N hN (𝟙 _) hk.symm rfl t₀ t₁ e₀ e₁

end Main

end ChiConst

universe u

open CategoryTheory CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory AlgebraicGeometry in
theorem solution
    {k : Type u} [Field k] {A : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k)) [IsProper a]
    (𝒱 : A.TwoAffineOpenCover) (L M : A.Modules)
    (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (h0 : RelPicard.IsAlgEquivZero a L) :
    (Module.finrank k (𝒱.sectionsOf a (L ⊗ M)).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf a (L ⊗ M)).H1
      = (Module.finrank k (𝒱.sectionsOf a M).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf a M).H1 :=
  ChiConst.main a 𝒱 L M hL hM h0

end S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_eulerChar_sectionsOf_tensor_eq
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_eulerChar_sectionsOf_tensor_eq (solution)
