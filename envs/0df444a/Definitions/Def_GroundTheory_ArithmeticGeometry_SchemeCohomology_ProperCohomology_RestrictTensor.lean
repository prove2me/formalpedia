-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_RestrictTensor
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_RestrictTensor
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T04:38:46.635519+00:00
-- url     : https://prove2.me/theorems/8ccf025d-401e-448d-8ac4-a4d8d2d0d153
-- title:
--   Restrict Tensor
-- statement:
--   Definitions and structural lemmas for Restrict Tensor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/RestrictTensor.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_TwistingSheaf
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsBasisOn_restrict
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsBasisOn_tmul
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_ext
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_add
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_mkSection
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_neg
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_sub
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_zero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_W_tensorToSheaf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_add
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_mkSection
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_neg
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_sub
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_zero


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory TensorProduct
universe u
noncomputable section
namespace RestrictTensor
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules) (U : X.Opens)
def ringInv : ringOn X U →+* ringOn Y (f ''ᵁ U) := (f.appIso U).inv.hom
def ringHom : ringOn Y (f ''ᵁ U) →+* ringOn X U := (f.appIso U).hom.hom
lemma ringInv_ringHom (r : ringOn Y (f ''ᵁ U)) : ringInv f U (ringHom f U r) = r := by
  change (f.appIso U).inv ((f.appIso U).hom r) = r
  exact (f.appIso U).hom_inv_id_apply r
def sec : ((preMod X).obj (M.restrict f)).obj (op U) →+ ((preMod Y).obj M).obj (op (f ''ᵁ U)) :=
  AddMonoidHom.id _
lemma sec_smul (r : ringOn X U) (m : ((preMod X).obj (M.restrict f)).obj (op U)) :
    sec f M U (r • m) = ringInv f U r • sec f M U m := rfl
def sec' : ((preMod Y).obj M).obj (op (f ''ᵁ U)) →+ ((preMod X).obj (M.restrict f)).obj (op U) :=
  AddMonoidHom.id _
lemma sec'_smul (r : ringOn Y (f ''ᵁ U)) (m : ((preMod Y).obj M).obj (op (f ''ᵁ U))) :
    sec' f M U (r • m) = ringHom f U r • sec' f M U m := by
  change r • m = ringInv f U (ringHom f U r) • m
  rw [ringInv_ringHom]
def toImage :
    ((preMod X).obj (M.restrict f)).obj (op U) ⊗[ringOn X U] ((preMod X).obj (N.restrict f)).obj (op U) →+
      ((preMod Y).obj M).obj (op (f ''ᵁ U)) ⊗[ringOn Y (f ''ᵁ U)]
        ((preMod Y).obj N).obj (op (f ''ᵁ U)) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (fun n => sec f M U m ⊗ₜ sec f N U n)
      (fun a b => by rw [map_add, tmul_add]))
      (fun a b => by ext n; simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add,
        add_tmul]))
    (fun r m n => by
      simp only [AddMonoidHom.mk'_apply, sec_smul]
      exact smul_tmul _ _ _)
lemma toImage_tmul (m : ((preMod X).obj (M.restrict f)).obj (op U))
    (n : ((preMod X).obj (N.restrict f)).obj (op U)) :
    toImage f M N U (m ⊗ₜ n) = sec f M U m ⊗ₜ sec f N U n := rfl
def ofImage :
    ((preMod Y).obj M).obj (op (f ''ᵁ U)) ⊗[ringOn Y (f ''ᵁ U)] ((preMod Y).obj N).obj (op (f ''ᵁ U)) →+
      ((preMod X).obj (M.restrict f)).obj (op U) ⊗[ringOn X U]
        ((preMod X).obj (N.restrict f)).obj (op U) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (fun n => sec' f M U m ⊗ₜ sec' f N U n)
      (fun a b => by rw [map_add, tmul_add]))
      (fun a b => by ext n; simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add,
        add_tmul]))
    (fun r m n => by
      simp only [AddMonoidHom.mk'_apply, sec'_smul]
      exact smul_tmul _ _ _)
lemma ofImage_toImage (z : ((preMod X).obj (M.restrict f)).obj (op U) ⊗[ringOn X U]
    ((preMod X).obj (N.restrict f)).obj (op U)) : ofImage f M N U (toImage f M N U z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb]
lemma toImage_ofImage (z : ((preMod Y).obj M).obj (op (f ''ᵁ U)) ⊗[ringOn Y (f ''ᵁ U)]
    ((preMod Y).obj N).obj (op (f ''ᵁ U))) : toImage f M N U (ofImage f M N U z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb]
lemma toImage_smul (r : ringOn X U) (z : ((preMod X).obj (M.restrict f)).obj (op U) ⊗[ringOn X U]
    ((preMod X).obj (N.restrict f)).obj (op U)) :
    toImage f M N U (r • z) = ringInv f U r • toImage f M N U z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
    rw [TensorProduct.smul_tmul', toImage_tmul, toImage_tmul, sec_smul, TensorProduct.smul_tmul']
  | add a b ha hb => rw [smul_add, map_add, map_add, ha, hb, smul_add]
def compApp : ((preMod X).obj (M.restrict f) ⊗ (preMod X).obj (N.restrict f)).obj (op U) →+
    ((preMod X).obj ((M ⊗ N).restrict f)).obj (op U) :=
  (sec' f (M ⊗ N) U).comp (((tensorToSheaf M N).app (op (f ''ᵁ U))).hom.toAddMonoidHom.comp
    (toImage f M N U))
lemma compApp_smul (r : ringOn X U)
    (z : ((preMod X).obj (M.restrict f) ⊗ (preMod X).obj (N.restrict f)).obj (op U)) :
    compApp f M N U (r • z) = r • compApp f M N U z := by
  change sec' f (M ⊗ N) U ((tensorToSheaf M N).app (op (f ''ᵁ U)) (toImage f M N U (r • z))) =
    sec' f (M ⊗ N) U (ringInv f U r • (tensorToSheaf M N).app (op (f ''ᵁ U)) (toImage f M N U z))
  exact congrArg (sec' f (M ⊗ N) U) ((congrArg ((tensorToSheaf M N).app (op (f ''ᵁ U))).hom
    (toImage_smul f M N U r z)).trans
      (((tensorToSheaf M N).app (op (f ''ᵁ U))).hom.map_smul (ringInv f U r) (toImage f M N U z)))
def comp : (preMod X).obj (M.restrict f) ⊗ (preMod X).obj (N.restrict f) ⟶
    (preMod X).obj ((M ⊗ N).restrict f) :=
  PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (compApp f M N U.unop)
      naturality := fun U V g => by
        ext z
        let L := (compApp f M N V.unop).comp (((preMod X).obj (M.restrict f) ⊗
          (preMod X).obj (N.restrict f)).map g).hom.toAddMonoidHom
        let R := (((preMod X).obj ((M ⊗ N).restrict f)).map g).hom.toAddMonoidHom.comp
          (compApp f M N U.unop)
        change L z = R z
        induction z using TensorProduct.induction_on with
        | zero => exact (map_zero L).trans (map_zero R).symm
        | tmul m n =>
          exact PresheafOfModules.naturality_apply (tensorToSheaf M N)
            (f.opensFunctor.map g.unop).op (sec f M U.unop m ⊗ₜ sec f N U.unop n)
        | add a b ha hb =>
          exact (map_add L a b).trans ((congrArg₂ (· + ·) ha hb).trans (map_add R a b).symm) }
    (fun U r z => compApp_smul f M N U.unop r z)
lemma toImage_map {U V : X.Opens} (h : V ≤ U)
    (z : ((preMod X).obj (M.restrict f) ⊗ (preMod X).obj (N.restrict f)).obj (op U)) :
    toImage f M N V (((preMod X).obj (M.restrict f) ⊗ (preMod X).obj (N.restrict f)).map
      (homOfLE h).op z) =
      (((preMod Y).obj M ⊗ (preMod Y).obj N).map (homOfLE (f.image_mono h)).op (toImage f M N U z)) := by
  let L := (toImage f M N V).comp (((preMod X).obj (M.restrict f) ⊗
    (preMod X).obj (N.restrict f)).map (homOfLE h).op).hom.toAddMonoidHom
  let R := (((preMod Y).obj M ⊗ (preMod Y).obj N).map
    (homOfLE (f.image_mono h)).op).hom.toAddMonoidHom.comp (toImage f M N U)
  change L z = R z
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero L).trans (map_zero R).symm
  | tmul m n => rfl
  | add a b ha hb => exact (map_add L a b).trans ((congrArg₂ (· + ·) ha hb).trans (map_add R a b).symm)
lemma W_comp : ModulesTensor.W (Opens.grothendieckTopology X) X.sheaf.obj (comp f M N) := by
  obtain ⟨hT₁, hT₂⟩ := (ModulesTensor.W_toPresheaf_iff (tensorToSheaf M N)).1 (W_tensorToSheaf M N)
  rw [ModulesTensor.W, MorphismProperty.inverseImage_iff, ModulesTensor.W_toPresheaf_iff]
  constructor
  · intro U z hz
    have h0 : (tensorToSheaf M N).app (op (f ''ᵁ U.unop)) (toImage f M N U.unop z) = 0 := hz
    have hS := hT₁ (op (f ''ᵁ U.unop)) _ h0
    rw [Opens.mem_grothendieckTopology] at hS ⊢
    intro x hx
    obtain ⟨W', i, hi, hxW'⟩ := hS (f x) ⟨x, hx, rfl⟩
    have hVU : f ⁻¹ᵁ W' ≤ U.unop := by
      rw [← f.preimage_image_eq U.unop]
      exact f.preimage_mono i.le
    refine ⟨f ⁻¹ᵁ W', homOfLE hVU, ?_, hxW'⟩
    have hi' : ((preMod Y).obj M ⊗ (preMod Y).obj N).map (homOfLE (f.image_mono hVU)).op
        (toImage f M N U.unop z) = 0 :=
      (ModulesTensor.zeroSieve _).downward_closed hi (homOfLE (f.image_preimage_le W'))
    change (((preMod X).obj (M.restrict f) ⊗ (preMod X).obj (N.restrict f)).map
      (homOfLE hVU).op z) = 0
    rw [← ofImage_toImage f M N (f ⁻¹ᵁ W') (((preMod X).obj (M.restrict f) ⊗
      (preMod X).obj (N.restrict f)).map (homOfLE hVU).op z), toImage_map]
    erw [hi', map_zero]
    rfl
  · intro U y
    have hS := hT₂ (op (f ''ᵁ U.unop)) y
    rw [Opens.mem_grothendieckTopology] at hS ⊢
    intro x hx
    obtain ⟨W', i, hi, hxW'⟩ := hS (f x) ⟨x, hx, rfl⟩
    have hVU : f ⁻¹ᵁ W' ≤ U.unop := by
      rw [← f.preimage_image_eq U.unop]
      exact f.preimage_mono i.le
    refine ⟨f ⁻¹ᵁ W', homOfLE hVU, ?_, hxW'⟩
    obtain ⟨w, hw⟩ := (ModulesTensor.imSieve _ _).downward_closed hi
      (homOfLE (f.image_preimage_le W'))
    refine ⟨ofImage f M N (f ⁻¹ᵁ W') w, ?_⟩
    change sec' f (M ⊗ N) _ ((tensorToSheaf M N).app _
      (toImage f M N (f ⁻¹ᵁ W') (ofImage f M N (f ⁻¹ᵁ W') w))) = _
    erw [toImage_ofImage]
    exact hw
def sheafifyIso : (sheafifyMod X).obj ((preMod X).obj (M.restrict f) ⊗ (preMod X).obj (N.restrict f)) ≅
    (M ⊗ N).restrict f :=
  haveI : IsIso ((sheafifyMod X).map (comp f M N)) :=
    Localization.inverts (modulesSheafification (Opens.grothendieckTopology X) X.sheaf)
      (ModulesTensor.W (Opens.grothendieckTopology X) X.sheaf.obj) _ (W_comp f M N)
  asIso ((sheafifyMod X).map (comp f M N)) ≪≫ asIso ((sheafifyModAdj X).counit.app _)
end RestrictTensor
open RestrictTensor in

def restrictTensorIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules) :
    (M ⊗ N).restrict f ≅ M.restrict f ⊗ N.restrict f :=
  (sheafifyIso f M N).symm ≪≫ tensorIso (M.restrict f) (N.restrict f)
attribute [local instance] MvPolynomial.gradedAlgebra in

def restrictTwistIso {A : Type u} [CommRing A] {n : ℕ} {U X : Scheme.{u}} (f : U ⟶ X)
    [IsOpenImmersion f] (i : X ⟶ projectiveSpace A n) (G : X.Modules) (k : ℤ) :
    ProjScheme.twist (f ≫ i) (G.restrict f) k ≅ (ProjScheme.twist i G k).restrict f :=
  (whiskerLeftIso (G.restrict f)
    (((Scheme.Modules.pullbackComp f i).app _).symm ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback f).app _).symm)) ≪≫
    (restrictTensorIso f G (ProjScheme.twistingSheaf i k)).symm
end
end GroundTheory.Arith.SchemeCoh


