-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.isLevelPairingValue_mul_of_iso_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8f3dde1e-995f-5902-a880-69b019e31895

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom
import Theorems.Thm_AlgebraicGeometry_RiemannForm_transportIso_tensorObj
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_mul_of_iso_tensor
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm"

noncomputable section

namespace MonoAddLevel

section Const

variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))

theorem IsConstScalar.conj {M N : A.Modules} (e : M ≅ N) {σ : N ⟶ N} {c : k}
    (hσ : IsConstScalar f σ c) : IsConstScalar f (e.hom ≫ σ ≫ e.inv) c := by
  intro U s
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app]
  change e.inv.app U (σ.app U (e.hom.app U s)) = _
  rw [hσ U, Scheme.Modules.Hom.app_smul]
  change _ • (e.hom.app U ≫ e.inv.app U) s = _ • s
  rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]
  rfl

end Const

section Transport

variable {A : Scheme.{0}} {T g : A ⟶ A} (h : T ≫ g = g)

theorem transportIso_naturality {M M' : A.Modules} (φ : M ⟶ M') :
    (Scheme.Modules.pullback T).map ((Scheme.Modules.pullback g).map φ) ≫ (transportIso h M').hom =
      (transportIso h M).hom ≫ (Scheme.Modules.pullback g).map φ := by
  have n := (Scheme.Modules.pullbackComp T g ≪≫ Scheme.Modules.pullbackCongr h).hom.naturality φ
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.comp_map] at n
  exact n

theorem transportIso_naturality_inv {M M' : A.Modules} (φ : M ⟶ M') :
    (transportIso h M).inv ≫ (Scheme.Modules.pullback T).map ((Scheme.Modules.pullback g).map φ) =
      (Scheme.Modules.pullback g).map φ ≫ (transportIso h M').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← transportIso_naturality h φ, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

theorem transportIso_inv_eq_of_iso {M M' : A.Modules} (φ : M ≅ M') :
    (transportIso h M).inv =
      (Scheme.Modules.pullback g).map φ.hom ≫ (transportIso h M').inv ≫
        (Scheme.Modules.pullback T).map ((Scheme.Modules.pullback g).map φ.inv) := by
  rw [← Category.assoc, ← transportIso_naturality_inv h φ.hom, Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, φ.hom_inv_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]

end Transport

theorem map_tensorHom {X Y : Scheme.{0}} (p : X ⟶ Y) {L L' M M' : Y.Modules} (φ : L ⟶ L') (ψ : M ⟶ M') :
    (Scheme.Modules.pullback p).map (φ ⊗ₘ ψ) =
      (Scheme.Modules.pullbackTensorObjIso p L M).hom ≫
        ((Scheme.Modules.pullback p).map φ ⊗ₘ (Scheme.Modules.pullback p).map ψ) ≫
        (Scheme.Modules.pullbackTensorObjIso p L' M').inv := by
  rw [← cancel_mono (Scheme.Modules.pullbackTensorObjIso p L' M').hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [Scheme.Modules.pullbackTensorObjIso, Iso.symm_hom, Functor.Monoidal.μIso_inv]
  exact (Functor.OplaxMonoidal.δ_natural (Scheme.Modules.pullback p) φ ψ).symm

theorem map_map_inv_hom_id_assoc {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (H : D ⥤ E) {X Y : C} (e : X ≅ Y) {Z : E} (k : H.obj (F.obj Y) ⟶ Z) :
    H.map (F.map e.inv) ≫ H.map (F.map e.hom) ≫ k = k := by
  rw [← Category.assoc, ← H.map_comp, Iso.map_inv_hom_id, H.map_id, Category.id_comp]

theorem sigma_tensor {A : Scheme.{0}} {T g : A ⟶ A} (h : T ≫ g = g) (q : A ⟶ A) (X Y : A.Modules)
    (βX : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback q).obj X) ≅ (Scheme.Modules.pullback g).obj X)
    (βY : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback q).obj Y) ≅ (Scheme.Modules.pullback g).obj Y)
    (β₀ : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback q).obj (X ⊗ Y)) ≅
        (Scheme.Modules.pullback g).obj (X ⊗ Y))
    (hβ₀ : β₀ =
      (Scheme.Modules.pullback g).mapIso (Scheme.Modules.pullbackTensorObjIso q X Y) ≪≫
        Scheme.Modules.pullbackTensorObjIso g ((Scheme.Modules.pullback q).obj X) ((Scheme.Modules.pullback q).obj Y) ≪≫
        (βX ⊗ᵢ βY) ≪≫ (Scheme.Modules.pullbackTensorObjIso g X Y).symm) :
    (β₀.symm ≪≫ (transportIso h ((Scheme.Modules.pullback q).obj (X ⊗ Y))).symm ≪≫
        (Scheme.Modules.pullback T).mapIso β₀ ≪≫ transportIso h (X ⊗ Y)).hom =
      (Scheme.Modules.pullbackTensorObjIso g X Y).hom ≫
        ((βX.symm ≪≫ (transportIso h ((Scheme.Modules.pullback q).obj X)).symm ≪≫
            (Scheme.Modules.pullback T).mapIso βX ≪≫ transportIso h X).hom ⊗ₘ
          (βY.symm ≪≫ (transportIso h ((Scheme.Modules.pullback q).obj Y)).symm ≪≫
            (Scheme.Modules.pullback T).mapIso βY ≪≫ transportIso h Y).hom) ≫
        (Scheme.Modules.pullbackTensorObjIso g X Y).inv := by
  subst hβ₀

  have e_tI : (transportIso h (X ⊗ Y)).hom =
      (Scheme.Modules.pullback T).map (Scheme.Modules.pullbackTensorObjIso g X Y).hom ≫
        (Scheme.Modules.pullbackTensorObjIso T ((Scheme.Modules.pullback g).obj X)
          ((Scheme.Modules.pullback g).obj Y)).hom ≫
        ((transportIso h X).hom ⊗ₘ (transportIso h Y).hom) ≫ (Scheme.Modules.pullbackTensorObjIso g X Y).inv := by
    rw [AlgebraicGeometry.RiemannForm.transportIso_tensorObj h X Y]
    simp only [Iso.trans_hom, Functor.mapIso_hom, tensorIso_hom, Iso.symm_hom]
  have e_tIG' : (transportIso h ((Scheme.Modules.pullback q).obj X ⊗ (Scheme.Modules.pullback q).obj Y)).inv =
      (Scheme.Modules.pullbackTensorObjIso g ((Scheme.Modules.pullback q).obj X) ((Scheme.Modules.pullback q).obj Y)).hom ≫
        ((transportIso h ((Scheme.Modules.pullback q).obj X)).inv ⊗ₘ
          (transportIso h ((Scheme.Modules.pullback q).obj Y)).inv) ≫
        (Scheme.Modules.pullbackTensorObjIso T
          ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback q).obj X))
          ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback q).obj Y))).inv ≫
        (Scheme.Modules.pullback T).map
          (Scheme.Modules.pullbackTensorObjIso g ((Scheme.Modules.pullback q).obj X)
            ((Scheme.Modules.pullback q).obj Y)).inv := by
    rw [AlgebraicGeometry.RiemannForm.transportIso_tensorObj h ((Scheme.Modules.pullback q).obj X) ((Scheme.Modules.pullback q).obj Y)]
    simp only [Iso.trans_inv, Functor.mapIso_inv, tensorIso_inv, Iso.symm_inv, Category.assoc]
  have e_tIG := transportIso_inv_eq_of_iso h (Scheme.Modules.pullbackTensorObjIso q X Y)
  rw [e_tIG'] at e_tIG
  have e_H := map_tensorHom T βX.hom βY.hom

  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    tensorIso_hom, tensorIso_inv, Functor.map_comp, Category.assoc]
  rw [e_tI, e_tIG, e_H]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.map_inv_hom_id_assoc, map_map_inv_hom_id_assoc]
  simp only [tensorHom_comp_tensorHom_assoc]

section Step0

variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)

theorem isLevelPairingValue_of_iso {𝓝 𝓝' : A.Modules} (e : 𝓝 ≅ 𝓝') (n : ℕ) (x y : Pt f) (c : k)
    (H : IsLevelPairingValue f L 𝓝' n x y c) : IsLevelPairingValue f L 𝓝 n x y c := by
  obtain ⟨hx, β, hβ⟩ := H
  refine ⟨hx, (Scheme.Modules.pullback (L.schemeNsmul n)).mapIso ((Scheme.Modules.pullback (translation f L y)).mapIso e) ≪≫
    β ≪≫ (Scheme.Modules.pullback (L.schemeNsmul n)).mapIso e.symm, ?_⟩
  have key : ((((Scheme.Modules.pullback (L.schemeNsmul n)).mapIso ((Scheme.Modules.pullback (translation f L y)).mapIso e) ≪≫
          β ≪≫ (Scheme.Modules.pullback (L.schemeNsmul n)).mapIso e.symm).symm ≪≫
        (transportIso hx ((Scheme.Modules.pullback (translation f L y)).obj 𝓝)).symm ≪≫
        (Scheme.Modules.pullback (translation f L x)).mapIso
          ((Scheme.Modules.pullback (L.schemeNsmul n)).mapIso ((Scheme.Modules.pullback (translation f L y)).mapIso e) ≪≫
            β ≪≫ (Scheme.Modules.pullback (L.schemeNsmul n)).mapIso e.symm) ≪≫
        transportIso hx 𝓝).hom) =
      ((Scheme.Modules.pullback (L.schemeNsmul n)).mapIso e).hom ≫
        (β.symm ≪≫ (transportIso hx ((Scheme.Modules.pullback (translation f L y)).obj 𝓝')).symm ≪≫
          (Scheme.Modules.pullback (translation f L x)).mapIso β ≪≫ transportIso hx 𝓝').hom ≫
        ((Scheme.Modules.pullback (L.schemeNsmul n)).mapIso e).inv := by
    have n1 := transportIso_naturality_inv hx ((Scheme.Modules.pullback (translation f L y)).map e.hom)
    have n2 := transportIso_naturality hx e.inv
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv,
      Functor.map_comp, Category.assoc]
    rw [reassoc_of% n1, n2]
    simp only [map_map_inv_hom_id_assoc]
  rw [key]
  exact IsConstScalar.conj f ((Scheme.Modules.pullback (L.schemeNsmul n)).mapIso e) hβ

end Step0

end MonoAddLevel

end

open MonoAddLevel in
theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    (𝓝 : A.Modules) (h𝓝 : Nonempty (𝓝 ≅ 𝓛 ⊗ 𝓜))
    (n : ℕ) (hn : (n : k) ≠ 0) (P Q : L.AlgPoints hc k) (hP : n • P = 0) (hQ : n • Q = 0) (c c' : k)
    (h₁ : IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint P) (RelativeGroupLaw.AlgPoints.toPoint Q) c)
    (h₂ : IsLevelPairingValue f L 𝓜 n (RelativeGroupLaw.AlgPoints.toPoint P) (RelativeGroupLaw.AlgPoints.toPoint Q) c') :
    IsLevelPairingValue f L 𝓝 n (RelativeGroupLaw.AlgPoints.toPoint P) (RelativeGroupLaw.AlgPoints.toPoint Q) (c * c') := by
  obtain ⟨e⟩ := h𝓝
  apply isLevelPairingValue_of_iso f L e
  obtain ⟨hx, βL, hL⟩ := h₁
  obtain ⟨hx', βM, hM⟩ := h₂
  refine ⟨hx, (Scheme.Modules.pullback (L.schemeNsmul n)).mapIso
      (Scheme.Modules.pullbackTensorObjIso (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q)) 𝓛 𝓜) ≪≫
    Scheme.Modules.pullbackTensorObjIso (L.schemeNsmul n) _ _ ≪≫ (βL ⊗ᵢ βM) ≪≫
    (Scheme.Modules.pullbackTensorObjIso (L.schemeNsmul n) 𝓛 𝓜).symm, ?_⟩
  rw [sigma_tensor hx (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q)) 𝓛 𝓜 βL βM _ rfl]
  exact IsConstScalar.conj f _
    (AlgebraicGeometry.RiemannForm.isConstScalar_tensorHom k f _ _ c c' hL hM)

end S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_mul_of_iso_tensor
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_mul_of_iso_tensor (solution)
