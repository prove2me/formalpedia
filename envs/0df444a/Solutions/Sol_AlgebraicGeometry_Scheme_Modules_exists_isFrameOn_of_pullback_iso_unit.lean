-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/9aab7e31-b7ba-552f-b423-ff7c9841999b

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit.AlgebraicGeometry"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits"

noncomputable section

namespace PresheafOfModules
p2m_export "PresheafOfModules" "presheaf sections pullback naturality_apply pushforward map map_comp_apply Hom unit free restriction obj InternalHom.map_id_apply"
p2m_open "PresheafOfModules"

namespace FrameBridge

open Opposite

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

structure TrivializationBelow (X₀ : Cᵒᵖ) where

  gen : ∀ {Y : Cᵒᵖ} (_ : X₀ ⟶ Y), F.obj Y
  compat : ∀ {Y Z : Cᵒᵖ} (f : X₀ ⟶ Y) (g : Y ⟶ Z), F.map g (gen f) = gen (f ≫ g)
  bij : ∀ {Y : Cᵒᵖ} (f : X₀ ⟶ Y), Function.Bijective (fun a : R.obj Y => a • gen f)

end FrameBridge

end PresheafOfModules

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme.Hom Scheme.Opens.ι_appIso Scheme.Hom.image_preimage_eq_opensRange_inf Scheme Scheme.Modules Scheme.Opens Scheme.Opens.opensRange_ι Scheme.Modules.IsFrameOn"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules.pullback Hom Γ Opens.ι_appIso Hom.image_preimage_eq_opensRange_inf Modules.restrictFunctor restrictFunctor Modules Opens grothendieckTopology Opens.opensRange_ι PresheafOfModules Modules.IsFrameOn"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pushforward pullback presheaf Hom restrictFunctor restrictFunctorIsoPullback map_smul IsInvertible IsFrameOn"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace FrameBridge

open TopologicalSpace Opposite PresheafOfModules.FrameBridge

variable {X : Scheme.{u}}

variable (U : X.Opens)

noncomputable def restrictRingCatSheafHom : (U : Scheme.{u}).ringCatSheaf ⟶
    (U.ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology (U : Scheme.{u})) (Opens.grothendieckTopology X)).obj
        X.ringCatSheaf :=
  ⟨𝟙 _⟩

noncomputable def restrictFunctor' : X.Modules ⥤ (U : Scheme.{u}).Modules :=
  SheafOfModules.pushforward (restrictRingCatSheafHom U)

lemma restrictFunctor'_eq : restrictFunctor' U = Modules.restrictFunctor U.ι := by
  dsimp only [restrictFunctor', Modules.restrictFunctor, restrictRingCatSheafHom]
  congr 2
  ext V : 2
  change 𝟙 _ = (forget₂ CommRingCat RingCat).map (U.ι.appIso V.unop).inv
  rw [Scheme.Opens.ι_appIso]
  rfl

noncomputable def restrictFunctor'IsoPullback : restrictFunctor' U ≅ Modules.pullback U.ι :=
  eqToIso (restrictFunctor'_eq U) ≪≫ restrictFunctorIsoPullback U.ι

variable {U} (L : X.Modules)

lemma image_preimage_of_le {V : X.Opens} (h : V ≤ U) : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr h

section

variable (e : (restrictFunctor' U).obj L ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)

noncomputable def gen₀ (W : (U : Scheme.{u}).Opens) : L.val.obj (op (U.ι ''ᵁ W)) :=
  (e.inv.val.app (op W)).hom (1 : Γ(U, W))

lemma gen₀_spec (W : (U : Scheme.{u}).Opens) (b : Γ(X, U.ι ''ᵁ W)) :
    (e.inv.val.app (op W)).hom b = b • gen₀ L e W := by
  have := (e.inv.val.app (op W)).hom.map_smul b (1 : Γ(U, W))
  rw [smul_eq_mul, mul_one] at this
  exact this

lemma gen₀_bijective (W : (U : Scheme.{u}).Opens) :
    Function.Bijective (fun b : Γ(X, U.ι ''ᵁ W) => b • gen₀ L e W) := by
  have h : Function.Bijective ((e.inv.val.app (op W)).hom) := by
    refine Function.bijective_iff_has_inverse.2 ⟨(e.hom.val.app (op W)).hom, fun b => ?_, fun m => ?_⟩
    · exact congr($(e.inv_hom_id).val.app (op W) |>.hom b)
    · exact congr($(e.hom_inv_id).val.app (op W) |>.hom m)
  exact (funext (gen₀_spec L e W) ▸ h :)

lemma gen₀_map {W W' : (U : Scheme.{u}).Opens} (i : W' ⟶ W) :
    L.val.map (U.ι.opensFunctor.map i).op (gen₀ L e W) = gen₀ L e W' := by
  have := PresheafOfModules.naturality_apply e.inv.val i.op (1 : Γ(U, W))

  rw [show ((SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf).val.map i.op) (1 : Γ(U, W)) =
    (1 : Γ(U, W')) from ((U : Scheme.{u}).presheaf.map i.op).hom.map_one] at this
  exact this.symm

omit e in

lemma bijective_smul_map_eqToHom {A B : X.Opens} (q : A = B) (t : L.val.obj (op A))
    (h : Function.Bijective (fun b : Γ(X, A) => b • t)) :
    Function.Bijective (fun a : Γ(X, B) => a • L.val.map (eqToHom q.symm : B ⟶ A).op t) := by
  subst q
  have e1 : L.val.map (eqToHom (rfl : A = A) : A ⟶ A).op t = t := by
    rw [eqToHom_refl, op_id]
    exact PresheafOfModules.InternalHom.map_id_apply (R := X.sheaf.obj) L.val _ _
  simpa only [e1] using h

noncomputable def trivializationBelow : TrivializationBelow L.val (op U) where
  gen {Y} f := L.val.map (eqToHom (image_preimage_of_le (U := U) f.unop.le).symm :
      Y.unop ⟶ U.ι ''ᵁ (U.ι ⁻¹ᵁ Y.unop)).op (gen₀ L e (U.ι ⁻¹ᵁ Y.unop))
  compat {Y Z} f g := by
    have hle : U.ι ⁻¹ᵁ Z.unop ≤ U.ι ⁻¹ᵁ Y.unop := fun x hx => g.unop.le hx
    dsimp only
    rw [← gen₀_map L e (homOfLE hle)]
    erw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
    exact congrFun (congrArg
      (fun φ : (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ Y.unop)) ⟶ Z) =>
        ((L.val.map φ).hom : L.val.obj (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ Y.unop))) → L.val.obj Z))
      (Subsingleton.elim _ _)) _
  bij {Y} f := bijective_smul_map_eqToHom L (image_preimage_of_le (U := U) f.unop.le) _
    (gen₀_bijective L e _)

end

end FrameBridge

open FrameBridge in

theorem exists_isFrameOn_of_pullback_iso_unit {X : Scheme.{u}} {M : X.Modules} (U : X.Opens)
    (eU : (Modules.pullback U.ι).obj M ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :
    ∃ s : Γ(M, U), IsFrameOn s U := by
  let e : (restrictFunctor' U).obj M ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf :=
    (restrictFunctor'IsoPullback U).app M ≪≫ eU
  let D := trivializationBelow M e
  refine ⟨D.gen (𝟙 (Opposite.op U)), ?_⟩
  intro W hWU _
  have hc : M.presheaf.map (homOfLE hWU).op (D.gen (𝟙 (Opposite.op U))) = D.gen (homOfLE hWU).op := by
    have h := D.compat (𝟙 (Opposite.op U)) (homOfLE hWU).op
    rw [Category.id_comp] at h
    exact h
  simp only [hc]
  exact D.bij (homOfLE hWU).op

end AlgebraicGeometry.Scheme.Modules

end

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit.AlgebraicGeometry in
theorem solution {X : Scheme.{u}} {M : X.Modules} (U : X.Opens)
    (eU : (Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :
    ∃ s : Γ(M, U), Scheme.Modules.IsFrameOn s U :=
  AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit U eU

end S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit (solution)
