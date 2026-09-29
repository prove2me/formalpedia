-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_trivialModDeformations_map_H1_tensor_natural
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/e6bf09d4-3695-58c8-94db-a3889f98de89

import Mathlib
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelPicardStageHom
import Theorems.Thm_TwoChartCech_Cover_squareZeroUnit_cohomologous_iff_and_exists
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_sectionsOf_equiv_lineBundle_one_add_of_pullback_quotient_isNilpotent
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_iff_exists_units_of_sectionsOf_equiv_lineBundle
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_pullback_stageHom_equiv_lineBundle_appLE
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_trivialModDeformations_map_H1_tensor_natural
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst"

set_option autoImplicit false

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra TrivSqZeroExt

noncomputable section

set_option quotPrecheck false

namespace P2mTJ2

section Generic

variable {X Y : Scheme.{u}}

theorem app_map {M N : X.Modules} (φ : M ⟶ N) {W₁ W₂ : X.Opens} (i : W₁ ⟶ W₂) (x : Γ(M, W₂)) :
    φ.app W₁ (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app W₂ x) :=
  PresheafOfModules.naturality_apply φ.val i.op x

def isoSections {L L' : X.Modules} (φ : L ≅ L') (U : X.Opens) : Γ(L, U) ≃ₗ[Γ(X, U)] Γ(L', U) where
  toFun := φ.hom.app U
  invFun := φ.inv.app U
  map_add' x y := map_add _ x y
  map_smul' r x := Scheme.Modules.Hom.app_smul _ r x
  left_inv x := by
    change (φ.hom.app U ≫ φ.inv.app U) x = x
    rw [← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
  right_inv x := by
    change (φ.inv.app U ≫ φ.hom.app U) x = x
    rw [← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl

def pullbackObjIsoOfEq {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback g).obj M :=
  (Scheme.Modules.pullbackCongr h).app M

def pullbackObjCompIso {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullback (f ≫ g)).obj M ≅
      (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) :=
  ((Scheme.Modules.pullbackComp f g).app M).symm

theorem nonempty_pullback_iso_unit (f : X ⟶ Y) {M : Y.Modules}
    (h : Nonempty (M ≅ SheafOfModules.unit Y.ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback f).obj M ≅ SheafOfModules.unit X.ringCatSheaf) :=
  ⟨(Scheme.Modules.pullback f).mapIso h.some ≪≫ Scheme.Modules.pullbackUnitIso f⟩

theorem nonempty_iso_unit_of_isIso_pullback (f : X ⟶ Y) [IsIso f] {M : Y.Modules}
    (h : Nonempty ((Scheme.Modules.pullback f).obj M ≅ SheafOfModules.unit X.ringCatSheaf)) :
    Nonempty (M ≅ SheafOfModules.unit Y.ringCatSheaf) :=
  ⟨((Scheme.Modules.pullbackId Y).app M).symm ≪≫
    pullbackObjIsoOfEq (IsIso.inv_hom_id f).symm M ≪≫
    pullbackObjCompIso (inv f) f M ≪≫
    (Scheme.Modules.pullback (inv f)).mapIso h.some ≪≫
    Scheme.Modules.pullbackUnitIso (inv f)⟩

theorem nonempty_iso_unit_of_isLocalRing {R : Type u} [CommRing R] [IsLocalRing R]
    {N : (Spec (CommRingCat.of R)).Modules} (hN : Scheme.Modules.IsInvertible N) :
    Nonempty (N ≅ SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf) := by
  obtain ⟨U, hxU, hU⟩ := hN.1 (IsLocalRing.closedPoint R)
  have hU' : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).mp hxU
  subst hU'
  haveI : IsIso (Scheme.Opens.ι (⊤ : (Spec (CommRingCat.of R)).Opens)) :=
    (inferInstance : IsIso (Spec (CommRingCat.of R)).topIso.hom)
  exact nonempty_iso_unit_of_isIso_pullback _ hU

variable {R : Type u} [CommRing R] (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))

def GluedBy (L : X.Modules) (t : (𝒱.cover c).A01ˣ) : Prop :=
  ∃ (e0 : (𝒱.sectionsOf c L).M0 ≃ₗ[(𝒱.cover c).A0] (𝒱.cover c).A0)
    (e1 : (𝒱.sectionsOf c L).M1 ≃ₗ[(𝒱.cover c).A1] (𝒱.cover c).A1)
    (e01 : (𝒱.sectionsOf c L).M01 ≃ₗ[(𝒱.cover c).A01] (𝒱.cover c).A01),
    (∀ x, e01 ((𝒱.sectionsOf c L).r0 x) = (𝒱.cover c).ρ0 (e0 x)) ∧
    (∀ y, e01 ((𝒱.sectionsOf c L).r1 y) = (t : (𝒱.cover c).A01) * (𝒱.cover c).ρ1 (e1 y))

theorem gluedBy_unit_one : GluedBy 𝒱 c (SheafOfModules.unit X.ringCatSheaf) 1 :=
  ⟨LinearEquiv.refl _ _, LinearEquiv.refl _ _, LinearEquiv.refl _ _, fun _ => rfl,
    fun _ => by rw [Units.val_one, one_mul]; rfl⟩

theorem gluedBy_of_iso {L L' : X.Modules} (φ : L ≅ L') {t : (𝒱.cover c).A01ˣ} (h : GluedBy 𝒱 c L t) :
    GluedBy 𝒱 c L' t := by
  obtain ⟨e0, e1, e01, he0, he1⟩ := h
  let ψ0 : (𝒱.sectionsOf c L').M0 ≃ₗ[(𝒱.cover c).A0] (𝒱.sectionsOf c L).M0 := isoSections φ.symm 𝒱.U0
  let ψ1 : (𝒱.sectionsOf c L').M1 ≃ₗ[(𝒱.cover c).A1] (𝒱.sectionsOf c L).M1 := isoSections φ.symm 𝒱.U1
  let ψ01 : (𝒱.sectionsOf c L').M01 ≃ₗ[(𝒱.cover c).A01] (𝒱.sectionsOf c L).M01 :=
    isoSections φ.symm (𝒱.U0 ⊓ 𝒱.U1)
  refine ⟨ψ0 ≪≫ₗ e0, ψ1 ≪≫ₗ e1, ψ01 ≪≫ₗ e01, fun x => ?_, fun y => ?_⟩
  · change e01 (φ.inv.app _ ((𝒱.sectionsOf c L').r0 x)) = (𝒱.cover c).ρ0 (e0 (φ.inv.app _ x))
    rw [← he0]
    exact congrArg e01 (app_map φ.inv _ x)
  · change e01 (φ.inv.app _ ((𝒱.sectionsOf c L').r1 y)) = _ * (𝒱.cover c).ρ1 (e1 (φ.inv.app _ y))
    rw [← he1]
    exact congrArg e01 (app_map φ.inv _ y)

theorem gluedBy_iff_of_iso {L L' : X.Modules} (φ : L ≅ L') (t : (𝒱.cover c).A01ˣ) :
    GluedBy 𝒱 c L t ↔ GluedBy 𝒱 c L' t :=
  ⟨gluedBy_of_iso 𝒱 c φ, gluedBy_of_iso 𝒱 c φ.symm⟩

theorem nonempty_iso_iff_of_gluedBy {L L' : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (hL' : Scheme.Modules.IsInvertible L') {t t' : (𝒱.cover c).A01ˣ} (h : GluedBy 𝒱 c L t)
    (h' : GluedBy 𝒱 c L' t') :
    Nonempty (L ≅ L') ↔ ∃ (a0 : (𝒱.cover c).A0ˣ) (a1 : (𝒱.cover c).A1ˣ),
      (t' : (𝒱.cover c).A01) =
        (𝒱.cover c).ρ0 (a0 : (𝒱.cover c).A0) * t * (𝒱.cover c).ρ1 ((a1⁻¹ : (𝒱.cover c).A1ˣ) : (𝒱.cover c).A1) := by
  obtain ⟨e0, e1, e01, he0, he1⟩ := h
  obtain ⟨e0', e1', e01', he0', he1'⟩ := h'
  exact AlgebraicGeometry.Scheme.TwoAffineOpenCover.nonempty_iso_iff_exists_units_of_sectionsOf_equiv_lineBundle
    𝒱 c hL hL' t t' e0 e1 e01 he0 he1 e0' e1' e01' he0' he1'

theorem exists_gluedBy (t : (𝒱.cover c).A01ˣ) : ∃ L : X.Modules, Scheme.Modules.IsInvertible L ∧ GluedBy 𝒱 c L t := by
  letI : Algebra (𝒱.cover c).A0 (𝒱.cover c).A01 := (𝒱.cover c).ρ0.toRingHom.toAlgebra
  letI : Algebra (𝒱.cover c).A1 (𝒱.cover c).A01 := (𝒱.cover c).ρ1.toRingHom.toAlgebra
  let rid0 := TensorProduct.AlgebraTensorModule.rid (𝒱.cover c).A0 (𝒱.cover c).A01 (𝒱.cover c).A01
  let rid1 := TensorProduct.AlgebraTensorModule.rid (𝒱.cover c).A1 (𝒱.cover c).A01 (𝒱.cover c).A01
  let σ : ((𝒱.cover c).A01 ⊗[(𝒱.cover c).A0] (𝒱.cover c).A0) ≃ₗ[(𝒱.cover c).A01]
      ((𝒱.cover c).A01 ⊗[(𝒱.cover c).A1] (𝒱.cover c).A1) :=
    rid0 ≪≫ₗ LinearEquiv.smulOfUnit t⁻¹ ≪≫ₗ rid1.symm
  have hrk0 : ∀ (F : Type u) [Field F] [Algebra (𝒱.cover c).A0 F],
      Module.finrank F (F ⊗[(𝒱.cover c).A0] (𝒱.cover c).A0) = 1 := fun F _ _ => by
    rw [(TensorProduct.AlgebraTensorModule.rid (𝒱.cover c).A0 F F).finrank_eq, Module.finrank_self]
  have hrk1 : ∀ (F : Type u) [Field F] [Algebra (𝒱.cover c).A1 F],
      Module.finrank F (F ⊗[(𝒱.cover c).A1] (𝒱.cover c).A1) = 1 := fun F _ _ => by
    rw [(TensorProduct.AlgebraTensorModule.rid (𝒱.cover c).A1 F F).finrank_eq, Module.finrank_self]
  obtain ⟨L, hL, e0, e1, e01, he0, he1⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_isInvertible_sectionsOf_equiv_of_projective 𝒱 c
      (𝒱.cover c).A0 (𝒱.cover c).A1 hrk0 hrk1 σ
  refine ⟨L, hL, e0, e1, e01 ≪≫ₗ rid0, fun m => ?_, fun m => ?_⟩
  · change rid0 (e01 ((𝒱.sectionsOf c L).r0 m)) = _
    rw [he0, TensorProduct.AlgebraTensorModule.rid_tmul]
    exact mul_one _
  · change rid0 (e01 ((𝒱.sectionsOf c L).r1 m)) = _
    have h := he1 m
    change rid1.symm (t⁻¹ • rid0 (e01 ((𝒱.sectionsOf c L).r1 m))) = _ at h
    rw [LinearEquiv.symm_apply_eq, TensorProduct.AlgebraTensorModule.rid_tmul, inv_smul_eq_iff] at h
    rw [h, Units.smul_def, smul_eq_mul]
    congr 1
    exact mul_one _

end Generic

section Charts

variable {K : Type u} [CommRing K] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of K))
variable (A : Type u) [CommRing A] [Algebra K A]

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover in

theorem exists_chartIsos :
    ∃ (e0 : (A ⊗[K] (𝒱.cover c).A0) ≃ₐ[A] ((𝒱.pullback c A).cover (pullback.snd c (specMap K A))).A0)
      (e1 : (A ⊗[K] (𝒱.cover c).A1) ≃ₐ[A] ((𝒱.pullback c A).cover (pullback.snd c (specMap K A))).A1)
      (e01 : (A ⊗[K] (𝒱.cover c).A01) ≃ₐ[A] ((𝒱.pullback c A).cover (pullback.snd c (specMap K A))).A01),
      (∀ s, e0 ((1 : A) ⊗ₜ[K] s) = ((pullback.fst c (specMap K A)).app 𝒱.U0).hom s) ∧
      (∀ s, e1 ((1 : A) ⊗ₜ[K] s) = ((pullback.fst c (specMap K A)).app 𝒱.U1).hom s) ∧
      (∀ s, e01 ((1 : A) ⊗ₜ[K] s) = ((pullback.fst c (specMap K A)).app (𝒱.U0 ⊓ 𝒱.U1)).hom s) := by
  obtain ⟨e0, e1, e01, -, -, h0, h1, h01, -, -⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_baseChangeIsos_structureSheaf 𝒱 c A
  exact ⟨e0, e1, e01, h0, h1, h01⟩

def E0 : (A ⊗[K] (𝒱.cover c).A0) ≃ₐ[A]
    ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap K A))).A0 :=
  (exists_chartIsos 𝒱 c A).choose

def E1 : (A ⊗[K] (𝒱.cover c).A1) ≃ₐ[A]
    ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap K A))).A1 :=
  (exists_chartIsos 𝒱 c A).choose_spec.choose

def E01 : (A ⊗[K] (𝒱.cover c).A01) ≃ₐ[A]
    ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap K A))).A01 :=
  (exists_chartIsos 𝒱 c A).choose_spec.choose_spec.choose

theorem E0_tmul (s : (𝒱.cover c).A0) : E0 𝒱 c A ((1 : A) ⊗ₜ[K] s) =
    ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap K A)).app 𝒱.U0).hom s :=
  (exists_chartIsos 𝒱 c A).choose_spec.choose_spec.choose_spec.1 s

theorem E1_tmul (s : (𝒱.cover c).A1) : E1 𝒱 c A ((1 : A) ⊗ₜ[K] s) =
    ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap K A)).app 𝒱.U1).hom s :=
  (exists_chartIsos 𝒱 c A).choose_spec.choose_spec.choose_spec.2.1 s

theorem E01_tmul (s : (𝒱.cover c).A01) : E01 𝒱 c A ((1 : A) ⊗ₜ[K] s) =
    ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap K A)).app (𝒱.U0 ⊓ 𝒱.U1)).hom s :=
  (exists_chartIsos 𝒱 c A).choose_spec.choose_spec.choose_spec.2.2 s

local notation "𝒰[" A "]" => Scheme.TwoAffineOpenCover.cover (Scheme.TwoAffineOpenCover.pullback 𝒱 c A)
  (pullback.snd c (Scheme.TwoAffineOpenCover.specMap K A))
local notation "𝒱[" A "]" => Scheme.TwoAffineOpenCover.pullback 𝒱 c A
local notation "p[" A "]" => pullback.fst c (Scheme.TwoAffineOpenCover.specMap K A)
local notation "q[" A "]" => pullback.snd c (Scheme.TwoAffineOpenCover.specMap K A)

theorem tmul_eq_mul (a : A) {B : Type u} [CommRing B] [Algebra K B] (s : B) :
    a ⊗ₜ[K] s = (a ⊗ₜ[K] (1 : B)) * ((1 : A) ⊗ₜ[K] s) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem E0_tmul_one (a : A) : E0 𝒱 c A (a ⊗ₜ[K] 1) = algebraMap A (𝒰[A]).A0 a :=
  (E0 𝒱 c A).commutes a

theorem E1_tmul_one (a : A) : E1 𝒱 c A (a ⊗ₜ[K] 1) = algebraMap A (𝒰[A]).A1 a :=
  (E1 𝒱 c A).commutes a

theorem E01_tmul_one (a : A) : E01 𝒱 c A (a ⊗ₜ[K] 1) = algebraMap A (𝒰[A]).A01 a :=
  (E01 𝒱 c A).commutes a

theorem E01_map_ρ0 (x : A ⊗[K] (𝒱.cover c).A0) :
    E01 𝒱 c A (Algebra.TensorProduct.map (AlgHom.id K A) (𝒱.cover c).ρ0 x) = (𝒰[A]).ρ0 (E0 𝒱 c A x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a s =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, tmul_eq_mul A a ((𝒱.cover c).ρ0 s), tmul_eq_mul A a s,
      map_mul, map_mul, map_mul, E01_tmul_one, E0_tmul_one, AlgHom.commutes, E01_tmul, E0_tmul]
    congr 1
    have := congrArg (fun φ => φ.hom s) ((p[A]).naturality (homOfLE (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0)).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    exact this

theorem E01_map_ρ1 (x : A ⊗[K] (𝒱.cover c).A1) :
    E01 𝒱 c A (Algebra.TensorProduct.map (AlgHom.id K A) (𝒱.cover c).ρ1 x) = (𝒰[A]).ρ1 (E1 𝒱 c A x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a s =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, tmul_eq_mul A a ((𝒱.cover c).ρ1 s), tmul_eq_mul A a s,
      map_mul, map_mul, map_mul, E01_tmul_one, E1_tmul_one, AlgHom.commutes, E01_tmul, E1_tmul]
    congr 1
    have := congrArg (fun φ => φ.hom s) ((p[A]).naturality (homOfLE (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1)).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    exact this

variable (A' : Type u) [CommRing A'] [Algebra K A'] [Algebra A A'] [IsScalarTower K A A']

local notation "σ[" A "," A' "]" =>
  RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom K (IsScalarTower.toAlgHom K A A'))

theorem appLE_congrHom {X' Y' : Scheme.{u}} {f g : X' ⟶ Y'} (h : f = g) (U : Y'.Opens) (V : X'.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

theorem baseChangeSnd_snd {T T' : Scheme.{u}} {t : T ⟶ Spec (.of K)} {t' : T' ⟶ Spec (.of K)}
    (s : SchemeHomOver t' t) : baseChangeSnd c s ≫ pullback.snd c t = pullback.snd c t' ≫ s.1 := by
  unfold baseChangeSnd
  exact pullback.lift_snd _ _ _

theorem stage_le : p[A'] ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1) ≤ σ[A,A'] ⁻¹ᵁ (p[A] ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1)) := by
  rw [← Scheme.Hom.comp_preimage, Scheme.TwoAffineOpenCover.baseChangeSnd_fst]

theorem stage_appLE_fst_app (s : (𝒱.cover c).A01) :
    ((σ[A,A']).appLE ((𝒱[A]).U0 ⊓ (𝒱[A]).U1) ((𝒱[A']).U0 ⊓ (𝒱[A']).U1)
        (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf 𝒱 c
          (RelPicard.LFP.stageHom K (IsScalarTower.toAlgHom K A A'))).ge).hom
      (((p[A]).app (𝒱.U0 ⊓ 𝒱.U1)).hom s) = ((p[A']).app (𝒱.U0 ⊓ 𝒱.U1)).hom s := by
  have key : (p[A]).app (𝒱.U0 ⊓ 𝒱.U1) ≫ (σ[A,A']).appLE ((p[A]) ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1))
      ((p[A']) ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1)) (stage_le 𝒱 c A A') = (p[A']).app (𝒱.U0 ⊓ 𝒱.U1) := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
      appLE_congrHom (Scheme.TwoAffineOpenCover.baseChangeSnd_fst c
        (RelPicard.LFP.stageHom K (IsScalarTower.toAlgHom K A A'))) _ _ _ le_rfl,
      Scheme.Hom.appLE_eq_app]
  have := congrArg (fun φ => φ.hom s) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this

theorem stage_appLE_algebraMap (a : A) :
    ((σ[A,A']).appLE ((𝒱[A]).U0 ⊓ (𝒱[A]).U1) ((𝒱[A']).U0 ⊓ (𝒱[A']).U1)
        (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf 𝒱 c
          (RelPicard.LFP.stageHom K (IsScalarTower.toAlgHom K A A'))).ge).hom
      (algebraMap A (𝒰[A]).A01 a) = algebraMap A' (𝒰[A']).A01 (algebraMap A A' a) := by

  have e2 : (p[A']) ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1) ≤ (q[A'] ≫ Spec.map (CommRingCat.ofHom (algebraMap A A'))) ⁻¹ᵁ ⊤ :=
    le_top
  have lhs : (Scheme.ΓSpecIso (.of A)).inv ≫ (q[A]).appLE ⊤ ((p[A]) ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1)) le_top ≫
      (σ[A,A']).appLE ((p[A]) ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1)) ((p[A']) ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1)) (stage_le 𝒱 c A A') =
      (Scheme.ΓSpecIso (.of A)).inv ≫
        (q[A'] ≫ Spec.map (CommRingCat.ofHom (algebraMap A A'))).appLE ⊤ ((p[A']) ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1)) e2 := by
    rw [Scheme.Hom.appLE_comp_appLE,
      appLE_congrHom (baseChangeSnd_snd c (RelPicard.LFP.stageHom K (IsScalarTower.toAlgHom K A A'))) _ _ _ e2]
    first | done | rfl
  have rhs : CommRingCat.ofHom (algebraMap A A') ≫ (Scheme.ΓSpecIso (.of A')).inv ≫
      (q[A']).appLE ⊤ ((p[A']) ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1)) le_top =
      (Scheme.ΓSpecIso (.of A)).inv ≫
        (q[A'] ≫ Spec.map (CommRingCat.ofHom (algebraMap A A'))).appLE ⊤ ((p[A']) ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1)) e2 := by
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    congr 1
  have key := lhs.trans rhs.symm
  have := congrArg (fun φ => φ.hom a) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  exact this

local notation "σ♯[" A "," A' "]" =>
  CommRingCat.Hom.hom (Scheme.Hom.appLE
    (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom K (IsScalarTower.toAlgHom K A A')))
    ((Scheme.TwoAffineOpenCover.pullback 𝒱 c A).U0 ⊓ (Scheme.TwoAffineOpenCover.pullback 𝒱 c A).U1)
    ((Scheme.TwoAffineOpenCover.pullback 𝒱 c A').U0 ⊓ (Scheme.TwoAffineOpenCover.pullback 𝒱 c A').U1)
    (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf 𝒱 c
      (RelPicard.LFP.stageHom K (IsScalarTower.toAlgHom K A A'))).ge)

theorem stage_appLE_E01 (x : A ⊗[K] (𝒱.cover c).A01) :
    (σ♯[A,A']) (E01 𝒱 c A x) =
      E01 𝒱 c A' (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K A A') (AlgHom.id K (𝒱.cover c).A01) x) := by
  have hzero : (σ♯[A,A']) (0 : (𝒰[A]).A01) = 0 := map_zero _
  have hadd : ∀ u v : (𝒰[A]).A01, (σ♯[A,A']) (u + v) = (σ♯[A,A']) u + (σ♯[A,A']) v := fun u v => map_add _ u v
  have hmul : ∀ u v : (𝒰[A]).A01, (σ♯[A,A']) (u * v) = (σ♯[A,A']) u * (σ♯[A,A']) v := fun u v => map_mul _ u v
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, hzero]; rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hadd, hx, hy]; rfl
  | tmul a s =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.toAlgHom_apply, tmul_eq_mul A a s,
      tmul_eq_mul A' (algebraMap A A' a) s, map_mul, map_mul, hmul, E01_tmul_one, E01_tmul_one, E01_tmul,
      E01_tmul, stage_appLE_fst_app, stage_appLE_algebraMap]
    rfl

end Charts

section SquareZero

variable {K : Type u} [Field K] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of K))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
variable (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
variable (W : Type u) [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

local notation "𝔸[" V "]" => TrivSqZeroExt K V
local notation "𝒰[" A "]" => Scheme.TwoAffineOpenCover.cover (Scheme.TwoAffineOpenCover.pullback 𝒱 c A)
  (pullback.snd c (Scheme.TwoAffineOpenCover.specMap K A))
local notation "𝒱[" A "]" => Scheme.TwoAffineOpenCover.pullback 𝒱 c A
local notation "p[" A "]" => pullback.fst c (Scheme.TwoAffineOpenCover.specMap K A)
local notation "q[" A "]" => pullback.snd c (Scheme.TwoAffineOpenCover.specMap K A)

local notation "red[" V "]" => Algebra.TensorProduct.lift ((Algebra.ofId K (𝒱.cover c).A01).comp (TrivSqZeroExt.fstHom K K V))
  (AlgHom.id K (𝒱.cover c).A01) (fun _ _ => Commute.all _ _)

local notation "vp[" V "]" => (fun x => (TensorProduct.comm K V (𝒱.cover c).A01).toLinearMap
  (TensorProduct.map (TrivSqZeroExt.sndHom K V) LinearMap.id x))

local notation "cls[" V "]" => (LinearMap.range (𝒱.cover c).structureSheaf.cechDiff).mkQ.rTensor V

local notation "u[" V "]" => Units.mapEquiv (E01 𝒱 c 𝔸[V]).toMulEquiv

def Nset (L : (pullback c (Scheme.TwoAffineOpenCover.specMap K 𝔸[V])).Modules) :
    Set ((𝔸[V] ⊗[K] (𝒱.cover c).A01)ˣ) :=
  {τ | red[V] (τ : 𝔸[V] ⊗[K] (𝒱.cover c).A01) = 1 ∧ GluedBy (𝒱[𝔸[V]]) (q[𝔸[V]]) L (u[V] τ)}

open Classical in

def βmod (L : (pullback c (Scheme.TwoAffineOpenCover.specMap K 𝔸[V])).Modules) :
    (𝒱.structureSheafSections c).H1 ⊗[K] V :=
  if h : (Nset 𝒱 c V L).Nonempty then cls[V] (vp[V] ((h.some : (𝔸[V] ⊗[K] (𝒱.cover c).A01)ˣ) :
    𝔸[V] ⊗[K] (𝒱.cover c).A01)) else 0

theorem coe_mapEquiv_symm_inv {M N : Type u} [Monoid M] [Monoid N] (h : M ≃* N) (a : Nˣ) :
    (((Units.mapEquiv h.symm a)⁻¹ : Mˣ) : M) = h.symm ((a⁻¹ : Nˣ) : N) := by
  rw [← map_inv]; rfl

theorem cobd_transport (τ τ' : (𝔸[V] ⊗[K] (𝒱.cover c).A01)ˣ) (a0 : (𝒰[𝔸[V]]).A0ˣ) (a1 : (𝒰[𝔸[V]]).A1ˣ)
    (h : ((u[V] τ' : (𝒰[𝔸[V]]).A01ˣ) : (𝒰[𝔸[V]]).A01) =
      (𝒰[𝔸[V]]).ρ0 (a0 : (𝒰[𝔸[V]]).A0) * (u[V] τ : (𝒰[𝔸[V]]).A01ˣ) *
        (𝒰[𝔸[V]]).ρ1 ((a1⁻¹ : (𝒰[𝔸[V]]).A1ˣ) : (𝒰[𝔸[V]]).A1)) :
    ∃ (b0 : (𝔸[V] ⊗[K] (𝒱.cover c).A0)ˣ) (b1 : (𝔸[V] ⊗[K] (𝒱.cover c).A1)ˣ),
      (τ' : 𝔸[V] ⊗[K] (𝒱.cover c).A01) =
        Algebra.TensorProduct.map (AlgHom.id K 𝔸[V]) (𝒱.cover c).ρ0 (b0 : 𝔸[V] ⊗[K] (𝒱.cover c).A0) *
          (τ : 𝔸[V] ⊗[K] (𝒱.cover c).A01) *
        Algebra.TensorProduct.map (AlgHom.id K 𝔸[V]) (𝒱.cover c).ρ1
          ((↑(b1⁻¹) : 𝔸[V] ⊗[K] (𝒱.cover c).A1)) := by
  refine ⟨Units.mapEquiv (E0 𝒱 c 𝔸[V]).toMulEquiv.symm a0, Units.mapEquiv (E1 𝒱 c 𝔸[V]).toMulEquiv.symm a1, ?_⟩
  rw [coe_mapEquiv_symm_inv]
  apply (E01 𝒱 c 𝔸[V]).injective
  rw [map_mul, map_mul, E01_map_ρ0, E01_map_ρ1]
  change _ = (𝒰[𝔸[V]]).ρ0 ((E0 𝒱 c 𝔸[V]) ((E0 𝒱 c 𝔸[V]).symm _)) * _ *
    (𝒰[𝔸[V]]).ρ1 ((E1 𝒱 c 𝔸[V]) ((E1 𝒱 c 𝔸[V]).symm _))
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  exact h

theorem cobd_transport' (τ τ' : (𝔸[V] ⊗[K] (𝒱.cover c).A01)ˣ) (b0 : (𝔸[V] ⊗[K] (𝒱.cover c).A0)ˣ)
    (b1 : (𝔸[V] ⊗[K] (𝒱.cover c).A1)ˣ)
    (h : (τ' : 𝔸[V] ⊗[K] (𝒱.cover c).A01) =
        Algebra.TensorProduct.map (AlgHom.id K 𝔸[V]) (𝒱.cover c).ρ0 (b0 : 𝔸[V] ⊗[K] (𝒱.cover c).A0) *
          (τ : 𝔸[V] ⊗[K] (𝒱.cover c).A01) *
        Algebra.TensorProduct.map (AlgHom.id K 𝔸[V]) (𝒱.cover c).ρ1
          ((↑(b1⁻¹) : 𝔸[V] ⊗[K] (𝒱.cover c).A1))) :
    ∃ (a0 : (𝒰[𝔸[V]]).A0ˣ) (a1 : (𝒰[𝔸[V]]).A1ˣ),
      ((u[V] τ' : (𝒰[𝔸[V]]).A01ˣ) : (𝒰[𝔸[V]]).A01) =
      (𝒰[𝔸[V]]).ρ0 (a0 : (𝒰[𝔸[V]]).A0) * (u[V] τ : (𝒰[𝔸[V]]).A01ˣ) *
        (𝒰[𝔸[V]]).ρ1 ((a1⁻¹ : (𝒰[𝔸[V]]).A1ˣ) : (𝒰[𝔸[V]]).A1) := by
  refine ⟨Units.mapEquiv (E0 𝒱 c 𝔸[V]).toMulEquiv b0, Units.mapEquiv (E1 𝒱 c 𝔸[V]).toMulEquiv b1, ?_⟩
  have h1 : (((Units.mapEquiv (E1 𝒱 c 𝔸[V]).toMulEquiv b1)⁻¹ : (𝒰[𝔸[V]]).A1ˣ) : (𝒰[𝔸[V]]).A1) =
      E1 𝒱 c 𝔸[V] ((b1⁻¹ : (𝔸[V] ⊗[K] (𝒱.cover c).A1)ˣ) : 𝔸[V] ⊗[K] (𝒱.cover c).A1) := by
    rw [← map_inv]; rfl
  rw [h1]
  change (E01 𝒱 c 𝔸[V]) _ = (𝒰[𝔸[V]]).ρ0 (E0 𝒱 c 𝔸[V] _) * (E01 𝒱 c 𝔸[V]) _ * _
  rw [h, map_mul, map_mul, E01_map_ρ0, E01_map_ρ1]

theorem cls_eq_of_mem_Nset {L : (pullback c (Scheme.TwoAffineOpenCover.specMap K 𝔸[V])).Modules}
    (hL : Scheme.Modules.IsInvertible L) {τ τ' : (𝔸[V] ⊗[K] (𝒱.cover c).A01)ˣ} (hτ : τ ∈ Nset 𝒱 c V L)
    (hτ' : τ' ∈ Nset 𝒱 c V L) :
    cls[V] (vp[V] (τ : 𝔸[V] ⊗[K] (𝒱.cover c).A01)) = cls[V] (vp[V] (τ' : 𝔸[V] ⊗[K] (𝒱.cover c).A01)) := by
  obtain ⟨a0, a1, h⟩ := (nonempty_iso_iff_of_gluedBy (𝒱[𝔸[V]]) (q[𝔸[V]]) hL hL hτ.2 hτ'.2).mp ⟨Iso.refl L⟩
  obtain ⟨b0, b1, hb⟩ := cobd_transport 𝒱 c V τ τ' a0 a1 h
  exact ((TwoChartCech.Cover.squareZeroUnit_cohomologous_iff_and_exists (𝒱.cover c) V).1 τ τ' hτ.1 hτ'.1).mp
    ⟨b0, b1, hb⟩

theorem βmod_eq_of_mem {L : (pullback c (Scheme.TwoAffineOpenCover.specMap K 𝔸[V])).Modules}
    (hL : Scheme.Modules.IsInvertible L) {τ : (𝔸[V] ⊗[K] (𝒱.cover c).A01)ˣ} (hτ : τ ∈ Nset 𝒱 c V L) :
    βmod 𝒱 c V L = cls[V] (vp[V] (τ : 𝔸[V] ⊗[K] (𝒱.cover c).A01)) := by
  have hne : (Nset 𝒱 c V L).Nonempty := ⟨τ, hτ⟩
  rw [βmod, dif_pos hne]
  exact cls_eq_of_mem_Nset 𝒱 c V hL hne.some_mem hτ

theorem Nset_iso {L L' : (pullback c (Scheme.TwoAffineOpenCover.specMap K 𝔸[V])).Modules} (φ : L ≅ L') :
    Nset 𝒱 c V L = Nset 𝒱 c V L' := by
  ext τ
  simp only [Nset, Set.mem_setOf_eq, gluedBy_iff_of_iso (𝒱[𝔸[V]]) (q[𝔸[V]]) φ]

theorem isNilpotent_kerIdeal : IsNilpotent (TrivSqZeroExt.kerIdeal K V) :=
  ⟨2, TrivSqZeroExt.kerIdeal_sq K V⟩

def gJ : pullback (q[𝔸[V]]) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (TrivSqZeroExt.kerIdeal K V)))) ⟶
    pullback c (𝟙 (Spec (CommRingCat.of K))) :=
  pullback.lift (pullback.fst _ _ ≫ p[𝔸[V]]) (pullback.fst _ _ ≫ p[𝔸[V]] ≫ c)
    (by simp only [Category.assoc, Category.comp_id])

theorem quot_comp :
    CommRingCat.ofHom (TrivSqZeroExt.fstHom K K V).toRingHom ≫ CommRingCat.ofHom (algebraMap K 𝔸[V]) ≫
        CommRingCat.ofHom (Ideal.Quotient.mk (TrivSqZeroExt.kerIdeal K V)) =
      CommRingCat.ofHom (Ideal.Quotient.mk (TrivSqZeroExt.kerIdeal K V)) := by
  ext a
  change Ideal.Quotient.mk _ (algebraMap K 𝔸[V] a.fst) = Ideal.Quotient.mk _ a
  rw [Ideal.Quotient.eq, TrivSqZeroExt.kerIdeal, RingHom.mem_ker, map_sub, TrivSqZeroExt.algebraMap_eq_inl',
    Algebra.algebraMap_self_apply]
  change (TrivSqZeroExt.inl a.fst : 𝔸[V]).fst - a.fst = 0
  rw [TrivSqZeroExt.fst_inl, sub_self]

theorem gJ_comp_i :
    gJ c V ≫ baseChangeSnd c (SquareZero.basePointOver K V) =
      pullback.fst (q[𝔸[V]]) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (TrivSqZeroExt.kerIdeal K V)))) := by
  apply pullback.hom_ext
  · unfold gJ baseChangeSnd
    rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, Category.comp_id]
    first | done | rfl
  · unfold gJ baseChangeSnd
    rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd]
    change (pullback.fst _ _ ≫ p[𝔸[V]] ≫ c) ≫ SquareZero.basePoint K V = pullback.fst _ _ ≫ q[𝔸[V]]
    rw [Category.assoc, Category.assoc, pullback.condition_assoc, pullback.condition, pullback.condition_assoc]
    congr 1
    rw [SquareZero.basePoint, ← Spec.map_comp, ← Spec.map_comp, Category.assoc, quot_comp]

theorem nonempty_Nset (L : TrivialModDeformations c ε V) :
    (Nset 𝒱 c V (show (pullback c (Scheme.TwoAffineOpenCover.specMap K 𝔸[V])).Modules from L.1.L)).Nonempty := by

  have hJ : Nonempty ((Scheme.Modules.pullback (pullback.fst (q[𝔸[V]])
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (TrivSqZeroExt.kerIdeal K V)))))).obj L.1.L ≅
      SheafOfModules.unit (pullback (q[𝔸[V]])
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (TrivSqZeroExt.kerIdeal K V))))).ringCatSheaf) :=
    ⟨pullbackObjIsoOfEq (gJ_comp_i c V).symm _ ≪≫ pullbackObjCompIso _ _ _ ≪≫
      (Scheme.Modules.pullback (gJ c V)).mapIso L.2.some ≪≫ Scheme.Modules.pullbackUnitIso _⟩
  obtain ⟨a, ha, e0, e1, e01, he0, he1⟩ :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_sectionsOf_equiv_lineBundle_one_add_of_pullback_quotient_isNilpotent
      (TrivSqZeroExt.kerIdeal K V) (isNilpotent_kerIdeal V) (q[𝔸[V]]) (𝒱[𝔸[V]]) L.1.isInvertible hJ

  have ha2 : IsNilpotent a := by
    refine ⟨2, ?_⟩
    have := Ideal.pow_mem_pow ha 2
    rwa [← Ideal.map_pow, TrivSqZeroExt.kerIdeal_sq, Ideal.map_bot, Ideal.mem_bot] at this
  let tL : (𝒰[𝔸[V]]).A01ˣ := ha2.isUnit_one_add.unit
  have htL : (tL : (𝒰[𝔸[V]]).A01) = 1 + a := rfl
  have hglued : GluedBy (𝒱[𝔸[V]]) (q[𝔸[V]]) L.1.L tL := ⟨e0, e1, e01, he0, fun y => by rw [htL]; exact he1 y⟩
  refine ⟨(u[V]).symm tL, ?_, ?_⟩
  ·
    have hcoe : (((u[V]).symm tL : (𝔸[V] ⊗[K] (𝒱.cover c).A01)ˣ) : 𝔸[V] ⊗[K] (𝒱.cover c).A01) =
        (E01 𝒱 c 𝔸[V]).symm (1 + a) := by rw [Units.mapEquiv_symm]; rfl
    rw [hcoe, map_add, map_one, map_add, map_one, add_eq_left]

    have hle : Ideal.map (algebraMap 𝔸[V] (𝒰[𝔸[V]]).A01) (TrivSqZeroExt.kerIdeal K V) ≤
        RingHom.ker ((red[V] : 𝔸[V] ⊗[K] (𝒱.cover c).A01 →+* (𝒱.cover c).A01).comp
          ((E01 𝒱 c 𝔸[V]).symm : (𝒰[𝔸[V]]).A01 →+* 𝔸[V] ⊗[K] (𝒱.cover c).A01)) := by
      rw [Ideal.map_le_iff_le_comap]
      intro j hj
      rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply]
      change red[V] ((E01 𝒱 c 𝔸[V]).symm (algebraMap 𝔸[V] (𝒰[𝔸[V]]).A01 j)) = 0
      rw [(E01 𝒱 c 𝔸[V]).symm.commutes j, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
        Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, mul_one, AlgHom.comp_apply]
      change algebraMap K _ ((TrivSqZeroExt.fstHom K K V) j) = 0
      rw [TrivSqZeroExt.kerIdeal, RingHom.mem_ker] at hj
      rw [hj, map_zero]
    have := hle ha
    rwa [RingHom.mem_ker, RingHom.comp_apply] at this
  · change GluedBy (𝒱[𝔸[V]]) (q[𝔸[V]]) L.1.L ((u[V]) ((u[V]).symm tL))
    rwa [MulEquiv.apply_symm_apply]

def βfun (L : TrivialModDeformations c ε V) : (𝒱.structureSheafSections c).H1 ⊗[K] V :=
  βmod 𝒱 c V (show (pullback c (Scheme.TwoAffineOpenCover.specMap K 𝔸[V])).Modules from L.1.L)

theorem βfun_eq_iff (L L' : TrivialModDeformations c ε V) :
    βfun 𝒱 c ε V L = βfun 𝒱 c ε V L' ↔ Nonempty (L.1.L ≅ L'.1.L) := by
  obtain ⟨τ, hτ⟩ := nonempty_Nset 𝒱 c ε V L
  obtain ⟨τ', hτ'⟩ := nonempty_Nset 𝒱 c ε V L'
  rw [βfun, βfun, βmod_eq_of_mem 𝒱 c V L.1.isInvertible hτ, βmod_eq_of_mem 𝒱 c V L'.1.isInvertible hτ']
  constructor
  · intro h
    obtain ⟨b0, b1, hb⟩ :=
      ((TwoChartCech.Cover.squareZeroUnit_cohomologous_iff_and_exists (𝒱.cover c) V).1 τ τ' hτ.1 hτ'.1).mpr h
    obtain ⟨a0, a1, ha⟩ := cobd_transport' 𝒱 c V τ τ' b0 b1 hb
    exact (nonempty_iso_iff_of_gluedBy (𝒱[𝔸[V]]) (q[𝔸[V]]) L.1.isInvertible L'.1.isInvertible hτ.2 hτ'.2).mpr
      ⟨a0, a1, ha⟩
  · rintro ⟨φ⟩
    have hτ'' : τ' ∈ Nset 𝒱 c V (show (pullback c (Scheme.TwoAffineOpenCover.specMap K 𝔸[V])).Modules from L.1.L) := by
      rw [Nset_iso 𝒱 c V φ]; exact hτ'
    exact cls_eq_of_mem_Nset 𝒱 c V L.1.isInvertible hτ hτ''

section Reduce

@[reducible] def algK : Algebra 𝔸[V] K := (TrivSqZeroExt.fstHom K K V).toRingHom.toAlgebra

attribute [local instance] algK

theorem isScalarTower_algK : IsScalarTower K 𝔸[V] K :=
  IsScalarTower.of_algebraMap_eq fun k => ((TrivSqZeroExt.fstHom K K V).commutes k).symm

attribute [local instance] isScalarTower_algK

local notation "σK[" V "]" =>
  RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom K (IsScalarTower.toAlgHom K 𝔸[V] K))

theorem lid_map_fst (x : 𝔸[V] ⊗[K] (𝒱.cover c).A01) :
    Algebra.TensorProduct.lid K (𝒱.cover c).A01
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K 𝔸[V] K) (AlgHom.id K (𝒱.cover c).A01) x) = red[V] x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a s =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.lid_tmul,
      Algebra.TensorProduct.lift_tmul, IsScalarTower.toAlgHom_apply, AlgHom.comp_apply, Algebra.ofId_apply,
      Algebra.smul_def]
    rfl

def jj : pullback c (Scheme.TwoAffineOpenCover.specMap K K) ⟶ pullback c (𝟙 (Spec (CommRingCat.of K))) :=
  baseChangeSnd c (⟨𝟙 _, by rw [Category.comp_id]; exact (Spec.map_id _).symm⟩ :
    SchemeHomOver (Scheme.TwoAffineOpenCover.specMap K K) (𝟙 (Spec (CommRingCat.of K))))

scoped instance : IsIso (jj c) := by
  unfold jj baseChangeSnd
  infer_instance

theorem jj_comp_i : jj c ≫ baseChangeSnd c (SquareZero.basePointOver K V) = σK[V] := by
  rw [jj, baseChangeSnd_comp]
  congr 1

theorem βfun_surjective : Function.Surjective (βfun 𝒱 c ε V) := by
  intro y
  obtain ⟨τ, hτ1, hτy⟩ := (TwoChartCech.Cover.squareZeroUnit_cohomologous_iff_and_exists (𝒱.cover c) V).2 y

  obtain ⟨L₀, hL₀, hglued⟩ := exists_gluedBy (𝒱[𝔸[V]]) (q[𝔸[V]]) (u[V] τ)
  obtain ⟨e0, e1, e01, he0, he1⟩ := hglued

  have hrig : Nonempty ((Scheme.Modules.pullback (rigSection c (SquareZero.toBase K V) ε)).obj L₀ ≅
      SheafOfModules.unit (Spec (CommRingCat.of 𝔸[V])).ringCatSheaf) :=
    nonempty_iso_unit_of_isLocalRing (hL₀.pullback _)
  let M₀ : RigidifiedLineBundle c ε (SquareZero.toBase K V) := ⟨L₀, hL₀, hrig⟩

  obtain ⟨e0', e1', e01', he0', he1'⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_sectionsOf_pullback_stageHom_equiv_lineBundle_appLE
      𝒱 c 𝔸[V] K L₀ hL₀ (u[V] τ) e0 e1 e01 he0 he1
  have hone : (show (𝒰[K]).A01 from ((σK[V]).appLE ((𝒱[𝔸[V]]).U0 ⊓ (𝒱[𝔸[V]]).U1) ((𝒱[K]).U0 ⊓ (𝒱[K]).U1)
      (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf 𝒱 c
        (RelPicard.LFP.stageHom K (IsScalarTower.toAlgHom K 𝔸[V] K))).ge).hom
      ((u[V] τ : (𝒰[𝔸[V]]).A01ˣ) : (𝒰[𝔸[V]]).A01)) = 1 := by
    change (CommRingCat.Hom.hom _) (E01 𝒱 c 𝔸[V] (τ : 𝔸[V] ⊗[K] (𝒱.cover c).A01)) = 1
    rw [stage_appLE_E01]
    have h1 : Algebra.TensorProduct.map (IsScalarTower.toAlgHom K 𝔸[V] K) (AlgHom.id K (𝒱.cover c).A01)
        (τ : 𝔸[V] ⊗[K] (𝒱.cover c).A01) = 1 := by
      apply (Algebra.TensorProduct.lid K (𝒱.cover c).A01).injective
      rw [lid_map_fst, hτ1, map_one]
    rw [h1, map_one]
    first | done | rfl
  have hgl1 : GluedBy (𝒱[K]) (q[K]) ((Scheme.Modules.pullback (σK[V])).obj L₀) 1 :=
    ⟨e0', e1', e01', he0', fun y => by rw [he1', hone, Units.val_one]⟩
  have htrivK : Nonempty ((Scheme.Modules.pullback (σK[V])).obj L₀ ≅
      SheafOfModules.unit (pullback c (Scheme.TwoAffineOpenCover.specMap K K)).ringCatSheaf) :=
    (nonempty_iso_iff_of_gluedBy (𝒱[K]) (q[K]) (hL₀.pullback _) (Scheme.Modules.isInvertible_unit _) hgl1
      (gluedBy_unit_one _ _)).mpr ⟨1, 1, by simp⟩

  have htriv1 : Nonempty ((M₀.pullbackAlong (SquareZero.basePointOver K V)).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) (𝟙 (Spec (CommRingCat.of K)))).L) := by
    refine nonempty_iso_unit_of_isIso_pullback (jj c) ⟨?_⟩
    exact (pullbackObjCompIso (jj c) (baseChangeSnd c (SquareZero.basePointOver K V)) L₀).symm ≪≫
      pullbackObjIsoOfEq (jj_comp_i c V) L₀ ≪≫ htrivK.some
  refine ⟨⟨M₀, htriv1⟩, ?_⟩
  have hN : τ ∈ Nset 𝒱 c V L₀ := ⟨hτ1, e0, e1, e01, he0, he1⟩
  rw [βfun, βmod_eq_of_mem 𝒱 c V hL₀ hN]
  exact hτy

end Reduce

section Natural

variable {V W}

theorem red_map (φ : V →ₗ[K] W) (x : 𝔸[V] ⊗[K] (𝒱.cover c).A01) :
    letI : Algebra 𝔸[V] 𝔸[W] := (TrivSqZeroExt.map φ).toRingHom.toAlgebra
    haveI : IsScalarTower K 𝔸[V] 𝔸[W] :=
      IsScalarTower.of_algebraMap_eq fun k => ((TrivSqZeroExt.map φ).commutes k).symm
    red[W] (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K 𝔸[V] 𝔸[W]) (AlgHom.id K (𝒱.cover c).A01) x) =
      red[V] x := by
  letI : Algebra 𝔸[V] 𝔸[W] := (TrivSqZeroExt.map φ).toRingHom.toAlgebra
  haveI : IsScalarTower K 𝔸[V] 𝔸[W] :=
    IsScalarTower.of_algebraMap_eq fun k => ((TrivSqZeroExt.map φ).commutes k).symm
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a s =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul,
      AlgHom.id_apply, IsScalarTower.toAlgHom_apply]
    congr 1
    change algebraMap K _ ((TrivSqZeroExt.map φ a).fst) = algebraMap K _ a.fst
    rw [TrivSqZeroExt.fst_map]

theorem vp_map (φ : V →ₗ[K] W) (x : 𝔸[V] ⊗[K] (𝒱.cover c).A01) :
    letI : Algebra 𝔸[V] 𝔸[W] := (TrivSqZeroExt.map φ).toRingHom.toAlgebra
    haveI : IsScalarTower K 𝔸[V] 𝔸[W] :=
      IsScalarTower.of_algebraMap_eq fun k => ((TrivSqZeroExt.map φ).commutes k).symm
    vp[W] (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K 𝔸[V] 𝔸[W]) (AlgHom.id K (𝒱.cover c).A01) x) =
      LinearMap.lTensor (𝒱.cover c).A01 φ (vp[V] x) := by
  letI : Algebra 𝔸[V] 𝔸[W] := (TrivSqZeroExt.map φ).toRingHom.toAlgebra
  haveI : IsScalarTower K 𝔸[V] 𝔸[W] :=
    IsScalarTower.of_algebraMap_eq fun k => ((TrivSqZeroExt.map φ).commutes k).symm
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a s =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.toAlgHom_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul, LinearMap.lTensor_tmul]
    congr 1
    change (TrivSqZeroExt.map φ a).snd = φ a.snd
    rw [TrivSqZeroExt.snd_map]

omit [Module Kᵐᵒᵖ V] [IsCentralScalar K V] [Module Kᵐᵒᵖ W] [IsCentralScalar K W] in
theorem cls_lTensor (φ : V →ₗ[K] W) (y : (𝒱.cover c).A01 ⊗[K] V) :
    cls[W] (LinearMap.lTensor (𝒱.cover c).A01 φ y) = LinearMap.lTensor _ φ (cls[V] y) := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
    LinearMap.lTensor_comp_rTensor]

theorem βfun_map (φ : V →ₗ[K] W) (L : TrivialModDeformations c ε V) :
    βfun 𝒱 c ε W (L.map φ) = LinearMap.lTensor ((𝒱.structureSheafSections c).H1) φ (βfun 𝒱 c ε V L) := by
  letI : Algebra 𝔸[V] 𝔸[W] := (TrivSqZeroExt.map φ).toRingHom.toAlgebra
  haveI : IsScalarTower K 𝔸[V] 𝔸[W] :=
    IsScalarTower.of_algebraMap_eq fun k => ((TrivSqZeroExt.map φ).commutes k).symm
  obtain ⟨τ, hτ⟩ := nonempty_Nset 𝒱 c ε V L
  obtain ⟨e0, e1, e01, he0, he1⟩ := hτ.2
  obtain ⟨e0', e1', e01', he0', he1'⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_sectionsOf_pullback_stageHom_equiv_lineBundle_appLE
      𝒱 c 𝔸[V] 𝔸[W] L.1.L L.1.isInvertible (u[V] τ) e0 e1 e01 he0 he1

  let τ' : (𝔸[W] ⊗[K] (𝒱.cover c).A01)ˣ :=
    Units.map (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K 𝔸[V] 𝔸[W]) (AlgHom.id K (𝒱.cover c).A01) :
      𝔸[V] ⊗[K] (𝒱.cover c).A01 →* 𝔸[W] ⊗[K] (𝒱.cover c).A01) τ
  have hτ' : (τ' : 𝔸[W] ⊗[K] (𝒱.cover c).A01) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom K 𝔸[V] 𝔸[W]) (AlgHom.id K (𝒱.cover c).A01)
        (τ : 𝔸[V] ⊗[K] (𝒱.cover c).A01) := rfl
  have hστ : (show (𝒰[𝔸[W]]).A01 from ((baseChangeSnd c (RelPicard.LFP.stageHom K
        (IsScalarTower.toAlgHom K 𝔸[V] 𝔸[W]))).appLE ((𝒱[𝔸[V]]).U0 ⊓ (𝒱[𝔸[V]]).U1) ((𝒱[𝔸[W]]).U0 ⊓ (𝒱[𝔸[W]]).U1)
      (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf 𝒱 c
        (RelPicard.LFP.stageHom K (IsScalarTower.toAlgHom K 𝔸[V] 𝔸[W]))).ge).hom
      ((u[V] τ : (𝒰[𝔸[V]]).A01ˣ) : (𝒰[𝔸[V]]).A01)) = ((u[W] τ' : (𝒰[𝔸[W]]).A01ˣ) : (𝒰[𝔸[W]]).A01) := by
    change (CommRingCat.Hom.hom _) (E01 𝒱 c 𝔸[V] (τ : 𝔸[V] ⊗[K] (𝒱.cover c).A01)) =
      E01 𝒱 c 𝔸[W] (τ' : 𝔸[W] ⊗[K] (𝒱.cover c).A01)
    rw [stage_appLE_E01, hτ']
  have hτ'N : τ' ∈ Nset 𝒱 c W ((Scheme.Modules.pullback (baseChangeSnd c (RelPicard.LFP.stageHom K
      (IsScalarTower.toAlgHom K 𝔸[V] 𝔸[W])))).obj L.1.L) := by
    refine ⟨?_, e0', e1', e01', he0', fun y => by rw [he1', hστ]⟩
    rw [hτ', red_map, hτ.1]
  have eqW : βfun 𝒱 c ε W (L.map φ) = cls[W] (vp[W] (τ' : 𝔸[W] ⊗[K] (𝒱.cover c).A01)) :=
    βmod_eq_of_mem 𝒱 c W (L.map φ).1.isInvertible hτ'N
  rw [eqW, βfun, βmod_eq_of_mem 𝒱 c V L.1.isInvertible hτ, hτ']
  change cls[W] (vp[W] _) = _
  rw [vp_map, cls_lTensor]

end Natural

end SquareZero

end P2mTJ2
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_trivialModDeformations_map_H1_tensor_natural.P2mTJ2"

theorem solution
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) (𝒱 : C.TwoAffineOpenCover) :
    ∃ β : ∀ (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V],
        TrivialModDeformations c ε V → (𝒱.structureSheafSections c).H1 ⊗[K] V,
      (∀ (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
          (L L' : TrivialModDeformations c ε V), β V L = β V L' ↔ Nonempty (L.1.L ≅ L'.1.L)) ∧
      (∀ (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V],
          Function.Surjective (β V)) ∧
      (∀ (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
          (W : Type u) [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]
          (φ : V →ₗ[K] W) (L : TrivialModDeformations c ε V),
          β W (L.map φ) = LinearMap.lTensor ((𝒱.structureSheafSections c).H1) φ (β V L)) :=
  ⟨fun V _ _ _ _ => P2mTJ2.βfun 𝒱 c ε V, fun V _ _ _ _ L L' => P2mTJ2.βfun_eq_iff 𝒱 c ε V L L',
    fun V _ _ _ _ => P2mTJ2.βfun_surjective 𝒱 c ε V,
    fun _ _ _ _ _ _ _ _ _ _ φ L => P2mTJ2.βfun_map 𝒱 c ε φ L⟩

end
end S_AlgebraicGeometry_RelPicard_exists_trivialModDeformations_map_H1_tensor_natural
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_trivialModDeformations_map_H1_tensor_natural (solution)
