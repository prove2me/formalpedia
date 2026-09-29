-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/e736d1de-5101-5b87-8377-dcbe9f114950

import Mathlib
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace Opposite TensorProduct"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "exists_basicOpen_le_affine_inter Scheme IsAffineOpen Scheme.Modules Scheme.IdealSheafData Scheme.Modules.sheafify Scheme.Modules.tensorIsoSheafify Scheme.IdealSheafData.IsInvertible"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "forget ringCatSheaf Hom Γ affineBasicOpen affineOpens basicOpen isBasis_affineOpens Modules Opens grothendieckTopology basicOpen_le PresheafOfModules IdealSheafData Modules.sheafify Modules.tensorIsoSheafify IdealSheafData.IsInvertible"
namespace IdealSheafData
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "ideal_mul map subscheme map_id ideal map_comp inclusion subschemeι map_ideal ker_subschemeι_app module IsInvertible"
p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}} (I : X.IdealSheafData)

private def _root_.AlgebraicGeometry.Scheme.IdealSheafData.sectionsIdeal (U : X.Opens) : Ideal Γ(X, U) :=
  RingHom.ker (I.subschemeι.app U).hom

p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "sectionsIdeal"
private lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.mem_sectionsIdeal_iff {U : X.Opens} (s : Γ(X, U)) :
    s ∈ I.sectionsIdeal U ↔ I.subschemeι.app U s = 0 := RingHom.mem_ker

p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "mem_sectionsIdeal_iff"

private lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.sectionsIdeal_eq_ideal (U : X.affineOpens) : I.sectionsIdeal U = I.ideal U :=
  I.ker_subschemeι_app U

p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "sectionsIdeal_eq_ideal"

private lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.map_mem_sectionsIdeal {U V : X.Opens} (i : V ⟶ U) {s : Γ(X, U)}
    (hs : s ∈ I.sectionsIdeal U) : X.presheaf.map i.op s ∈ I.sectionsIdeal V := by
  rw [mem_sectionsIdeal_iff] at hs ⊢
  have := ConcreteCategory.congr_hom (I.subschemeι.naturality i.op) s
  simp only [CommRingCat.comp_apply] at this

  erw [this, hs, map_zero]

p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "map_mem_sectionsIdeal"

def sectionsPresheaf : (X.Opens)ᵒᵖ ⥤ Ab.{u} where
  obj U := AddCommGrpCat.of (I.sectionsIdeal U.unop)
  map {U V} i := AddCommGrpCat.ofHom
    { toFun := fun s => ⟨X.presheaf.map i s.1, I.map_mem_sectionsIdeal i.unop s.2⟩
      map_zero' := Subtype.ext (by
        change X.presheaf.map i (0 : Γ(X, U.unop)) = 0
        exact map_zero _)
      map_add' := fun s t => Subtype.ext (by
        change X.presheaf.map i (s.1 + t.1) = X.presheaf.map i s.1 + X.presheaf.map i t.1
        exact map_add _ _ _) }
  map_id U := by
    ext s
    change X.presheaf.map (𝟙 U) s.1 = s.1
    rw [X.presheaf.map_id]
    rfl
  map_comp i j := by
    ext s
    change X.presheaf.map (i ≫ j) s.1 = X.presheaf.map j (X.presheaf.map i s.1)
    rw [X.presheaf.map_comp]
    rfl

scoped instance (U : (X.Opens)ᵒᵖ) : Module ((X.ringCatSheaf.obj).obj U) ((sectionsPresheaf I).obj U) :=
  inferInstanceAs (Module Γ(X, U.unop) (I.sectionsIdeal U.unop))

lemma sectionsPresheaf_map_apply_coe {U V : (X.Opens)ᵒᵖ} (i : U ⟶ V)
    (s : (sectionsPresheaf I).obj U) :
    ((sectionsPresheaf I).map i s).1 = X.presheaf.map i s.1 := rfl

def toPresheafOfModules : X.PresheafOfModules :=
  PresheafOfModules.ofPresheaf (sectionsPresheaf I) (by
    intro U V i r s
    apply Subtype.ext
    change X.presheaf.map i ((show Γ(X, U.unop) from r) * s.1) =
      (show Γ(X, V.unop) from X.presheaf.map i (show Γ(X, U.unop) from r)) * X.presheaf.map i s.1
    exact map_mul _ _ _)

@[scoped simp] lemma toPresheafOfModules_presheaf : (toPresheafOfModules I).presheaf = sectionsPresheaf I :=
  rfl

def sectionsSubfunctor : Subfunctor (X.presheaf ⋙ CategoryTheory.forget CommRingCat) where
  obj U := {s | s ∈ I.sectionsIdeal U.unop}
  map {U V} i s hs := I.map_mem_sectionsIdeal i.unop hs

def sectionsIso : sectionsPresheaf I ⋙ CategoryTheory.forget Ab ≅ (sectionsSubfunctor I).toFunctor :=
  NatIso.ofComponents (fun U => Equiv.toIso
    { toFun := fun s => ⟨s.1, s.2⟩
      invFun := fun s => ⟨s.1, s.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) (by intros; rfl)

lemma mem_sectionsIdeal_of_locally {U : X.Opens} (s : Γ(X, U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (_ : V ≤ U), x ∈ V ∧
      X.presheaf.map (homOfLE ‹V ≤ U›).op s ∈ I.sectionsIdeal V) :
    s ∈ I.sectionsIdeal U := by
  rw [mem_sectionsIdeal_iff]

  let ι : Type u := {V : X.Opens // ∃ (_ : V ≤ U), X.presheaf.map (homOfLE ‹V ≤ U›).op s ∈
    I.sectionsIdeal V}
  let W : ι → I.subscheme.Opens := fun V => I.subschemeι ⁻¹ᵁ V.1
  have hcover : I.subschemeι ⁻¹ᵁ U ≤ iSup W := by
    intro z hz
    obtain ⟨V, hVU, hzV, hV⟩ := h _ hz
    exact Opens.mem_iSup.2 ⟨⟨V, hVU, hV⟩, hzV⟩
  refine I.subscheme.sheaf.eq_of_locally_eq' W (I.subschemeι ⁻¹ᵁ U)
    (fun V => homOfLE (fun z hz => V.2.1 hz)) hcover _ _ (fun V => ?_)
  obtain ⟨hVU, hV⟩ := V.2
  rw [mem_sectionsIdeal_iff] at hV
  have nat := ConcreteCategory.congr_hom (I.subschemeι.naturality (homOfLE hVU).op) s
  simp only [CommRingCat.comp_apply] at nat
  rw [map_zero]
  erw [← nat]
  exact hV

lemma isSheaf_toPresheafOfModules :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (toPresheafOfModules I).presheaf := by
  have hO : Presieve.IsSheaf (Opens.grothendieckTopology X)
      (X.presheaf ⋙ CategoryTheory.forget CommRingCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      ((Presheaf.isSheaf_iff_isSheaf_comp _ X.sheaf.obj (CategoryTheory.forget CommRingCat)).1
        X.sheaf.property)
  rw [toPresheafOfModules_presheaf,
    Presheaf.isSheaf_iff_isSheaf_comp (Opens.grothendieckTopology X) (sectionsPresheaf I)
      (CategoryTheory.forget Ab),
    Presheaf.isSheaf_of_iso_iff (sectionsIso I), isSheaf_iff_isSheaf_of_type,
    Subfunctor.isSheaf_iff _ hO]
  intro U s hs
  apply mem_sectionsIdeal_of_locally
  intro x hx
  obtain ⟨V, i, hi, hxV⟩ := hs x hx
  exact ⟨V, i.le, hxV, hi⟩

private def _root_.AlgebraicGeometry.Scheme.IdealSheafData.toModule : X.Modules where
  val := toPresheafOfModules I
  isSheaf := isSheaf_toPresheafOfModules I

p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "toModule"

lemma toModule_sections (U : X.Opens) :
    ((toModule I).val.obj (op U) : Type u) = I.sectionsIdeal U := rfl

private def _root_.AlgebraicGeometry.Scheme.IdealSheafData.toModuleι : toModule I ⟶ SheafOfModules.unit X.ringCatSheaf :=
  ⟨{ app := fun U => ModuleCat.ofHom
      { toFun := fun s => s.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
     naturality := fun i => by ext s; rfl }⟩

p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "toModuleι"
example : (SheafOfModules.unit X.ringCatSheaf : X.Modules) = 𝟙_ X.Modules := rfl

lemma toModuleι_app_apply (U : (X.Opens)ᵒᵖ) (s : (toModule I).val.obj U) :
    (toModuleι I).val.app U s = s.1 := rfl

scoped instance (U : (X.Opens)ᵒᵖ) : Mono ((toModuleι I).val.app U) :=
  (ModuleCat.mono_iff_injective _).2 (fun s t h => by apply Subtype.ext; exact h)

lemma toModuleι_comp_unitToPushforwardUnit :
    (I.toModuleι : (I.toModule : SheafOfModules X.ringCatSheaf) ⟶
        SheafOfModules.unit X.ringCatSheaf) ≫ I.subschemeι.unitToPushforwardUnit = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext s
  change (I.subschemeι.unitToPushforwardUnit).val.app U ((I.toModuleι).val.app U s) = 0
  erw [SheafOfModules.unitToPushforwardObjUnit_val_app_apply]
  exact (I.mem_sectionsIdeal_iff s.1).1 s.2

def isLimitKernelFork : IsLimit (KernelFork.ofι
    (I.toModuleι : (I.toModule : SheafOfModules X.ringCatSheaf) ⟶ SheafOfModules.unit X.ringCatSheaf)
    (toModuleι_comp_unitToPushforwardUnit I)) :=
  KernelFork.IsLimit.ofι _ _
    (fun {M} φ hφ => ⟨{
      app := fun U => ModuleCat.ofHom
        { toFun := fun m => (⟨φ.val.app U m, by
            rw [mem_sectionsIdeal_iff]
            have h := congr_arg (fun k : M ⟶ _ => k.val.app U m) hφ
            change (I.subschemeι.unitToPushforwardUnit).val.app U (φ.val.app U m) = 0 at h
            erw [SheafOfModules.unitToPushforwardObjUnit_val_app_apply] at h
            exact h⟩ : I.sectionsIdeal U.unop)
          map_add' := fun m m' => Subtype.ext (by
            change φ.val.app U (m + m') = φ.val.app U m + φ.val.app U m'
            exact map_add _ _ _)
          map_smul' := fun r m => Subtype.ext (by
            change φ.val.app U (r • m) = r • φ.val.app U m
            exact (φ.val.app U).hom.map_smul r m) }
      naturality := fun {U V} i => by
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro m
        apply Subtype.ext
        exact PresheafOfModules.naturality_apply φ.val i m }⟩)
    (fun {M} φ hφ => by
      apply SheafOfModules.hom_ext; apply PresheafOfModules.hom_ext; intro U; ext m; rfl)
    (fun {M} φ hφ m hm => by
      apply SheafOfModules.hom_ext; apply PresheafOfModules.hom_ext; intro U; ext x
      apply Subtype.ext
      change ((m ≫ I.toModuleι).val.app U) x = φ.val.app U x
      rw [hm])

def moduleIsoToModule : (I.module : SheafOfModules X.ringCatSheaf) ≅ I.toModule :=
  IsLimit.conePointUniqueUpToIso (kernelIsKernel _) (isLimitKernelFork I)

omit I in

lemma exists_affineOpen_le {U : X.Opens} {x : X} (hx : x ∈ U) :
    ∃ V : X.affineOpens, x ∈ (V : X.Opens) ∧ (V : X.Opens) ≤ U := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  exact ⟨⟨V, hV⟩, hxV, hVU⟩

variable (J : X.IdealSheafData)

lemma mul_mem_sectionsIdeal_mul {U : X.Opens} {s t : Γ(X, U)} (hs : s ∈ I.sectionsIdeal U)
    (ht : t ∈ J.sectionsIdeal U) : s * t ∈ (I * J).sectionsIdeal U := by
  apply mem_sectionsIdeal_of_locally
  intro x hx
  obtain ⟨V, hxV, hVU⟩ := exists_affineOpen_le (X := X) hx
  refine ⟨V, hVU, hxV, ?_⟩
  rw [map_mul, sectionsIdeal_eq_ideal, ideal_mul, Pi.mul_apply]
  apply Ideal.mul_mem_mul
  · rw [← sectionsIdeal_eq_ideal]; exact I.map_mem_sectionsIdeal _ hs
  · rw [← sectionsIdeal_eq_ideal]; exact J.map_mem_sectionsIdeal _ ht

lemma sectionsIdeal_mul_eq (W : X.Opens) (hW : IsAffineOpen W) :
    (I * J).sectionsIdeal W = I.sectionsIdeal W * J.sectionsIdeal W := by
  rw [sectionsIdeal_eq_ideal (I * J) ⟨W, hW⟩, ideal_mul, Pi.mul_apply,
    ← sectionsIdeal_eq_ideal I ⟨W, hW⟩, ← sectionsIdeal_eq_ideal J ⟨W, hW⟩]

def mulApp (U : (X.Opens)ᵒᵖ) :
    ((toModule I).val ⊗ (toModule J).val).obj U ⟶ (toModule (I * J)).val.obj U :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun s t => (⟨s.1 * t.1, mul_mem_sectionsIdeal_mul I J s.2 t.2⟩ : (I * J).sectionsIdeal U.unop))
    (fun s s' t => Subtype.ext (add_mul s.1 s'.1 t.1))
    (fun c s t => Subtype.ext (mul_assoc (show Γ(X, U.unop) from c) s.1 t.1))
    (fun s t t' => Subtype.ext (mul_add s.1 t.1 t'.1))
    (fun c s t => Subtype.ext (mul_left_comm s.1 (show Γ(X, U.unop) from c) t.1))

lemma mulApp_tmul (U : (X.Opens)ᵒᵖ) (s : (toModule I).val.obj U) (t : (toModule J).val.obj U) :
    (DFunLike.coe (α := (((toModule I).val ⊗ (toModule J).val).obj U :))
      (β := fun _ => (toModule (I * J)).val.obj U)
      (mulApp I J U).hom (s ⊗ₜ[Γ(X, U.unop)] t)).1 = s.1 * t.1 := by
  letI : CommRing ((X.ringCatSheaf.obj).obj U) := inferInstanceAs (CommRing Γ(X, U.unop))
  erw [ModuleCat.MonoidalCategory.tensorLift_tmul]

def mulMap : (toModule I).val ⊗ (toModule J).val ⟶ (toModule (I * J)).val where
  app U := mulApp I J U
  naturality {U V} i := ModuleCat.MonoidalCategory.tensor_ext (fun s t => by
    apply Subtype.ext
    change (DFunLike.coe (α := (((toModule I).val ⊗ (toModule J).val).obj V :))
      (β := fun _ => (toModule (I * J)).val.obj V) (mulApp I J V).hom
        (DFunLike.coe (α := (((toModule I).val ⊗ (toModule J).val).obj U :))
          (β := fun _ => (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i).hom).obj
            (((toModule I).val ⊗ (toModule J).val).obj V))
          (ModuleCat.Hom.hom (((toModule I).val ⊗ (toModule J).val).map i))
            (s ⊗ₜ[Γ(X, U.unop)] t))).1 =
      X.presheaf.map i (DFunLike.coe (α := (((toModule I).val ⊗ (toModule J).val).obj U :))
        (β := fun _ => (toModule (I * J)).val.obj U) (mulApp I J U).hom (s ⊗ₜ[Γ(X, U.unop)] t)).1
    erw [_root_.PresheafOfModules.tensorObj_map_tmul' (R := X.sheaf.obj)
      ((toModule I).val) (G := (toModule J).val) i s t]
    erw [mulApp_tmul, mulApp_tmul]
    exact (map_mul (X.presheaf.map i).hom s.1 t.1).symm)

lemma mulMap_app_tmul (U : (X.Opens)ᵒᵖ) (s : (toModule I).val.obj U) (t : (toModule J).val.obj U) :
    (DFunLike.coe (α := (((toModule I).val ⊗ (toModule J).val).obj U :))
      (β := fun _ => (toModule (I * J)).val.obj U)
      ((mulMap I J).app U).hom (s ⊗ₜ[Γ(X, U.unop)] t)).1 = s.1 * t.1 :=
  mulApp_tmul I J U s t

section good

variable {I J}
variable {W : X.Opens} (hW : IsAffineOpen W) (a b : Γ(X, W))
  (ha : a ∈ nonZeroDivisors Γ(X, W)) (hb : b ∈ nonZeroDivisors Γ(X, W))
  (hIa : I.sectionsIdeal W = Ideal.span {a}) (hJb : J.sectionsIdeal W = Ideal.span {b})

omit I J in

def genEquiv (K : X.IdealSheafData) (g : Γ(X, W)) (hg : g ∈ nonZeroDivisors Γ(X, W))
    (hKg : K.sectionsIdeal W = Ideal.span {g}) : Γ(X, W) ≃ₗ[Γ(X, W)] K.sectionsIdeal W :=
  LinearEquiv.ofBijective
    { toFun := fun c => ⟨c * g, hKg ▸ Ideal.mul_mem_left _ c (Ideal.subset_span rfl)⟩
      map_add' := fun c c' => Subtype.ext (add_mul c c' g)
      map_smul' := fun c c' => Subtype.ext (mul_assoc c c' g) }
    (by
      constructor
      · intro c c' h
        exact (mul_cancel_right_mem_nonZeroDivisors hg).1 (congrArg Subtype.val h)
      · rintro ⟨u, hu⟩
        rw [hKg, Ideal.mem_span_singleton'] at hu
        obtain ⟨c, hc⟩ := hu
        exact ⟨c, Subtype.ext hc⟩)

omit I J in
lemma genEquiv_apply_coe (K : X.IdealSheafData) (g : Γ(X, W)) (hg : g ∈ nonZeroDivisors Γ(X, W))
    (hKg : K.sectionsIdeal W = Ideal.span {g}) (c : Γ(X, W)) :
    (genEquiv K g hg hKg c).1 = c * g := rfl

omit I J in
lemma smul_genEquiv_one (K : X.IdealSheafData) (g : Γ(X, W)) (hg : g ∈ nonZeroDivisors Γ(X, W))
    (hKg : K.sectionsIdeal W = Ideal.span {g}) (c : Γ(X, W)) :
    c • genEquiv K g hg hKg 1 = genEquiv K g hg hKg c :=
  Subtype.ext (by change c * (1 * g) = c * g; rw [one_mul])

omit I J in
lemma genEquiv_symm_smul (K : X.IdealSheafData) (g : Γ(X, W)) (hg : g ∈ nonZeroDivisors Γ(X, W))
    (hKg : K.sectionsIdeal W = Ideal.span {g}) (u : K.sectionsIdeal W) :
    (genEquiv K g hg hKg).symm u • (genEquiv K g hg hKg 1) = u := by
  rw [smul_genEquiv_one, LinearEquiv.apply_symm_apply]

include hW ha hb hIa hJb in

lemma mulApp_bijective : Function.Bijective (mulApp I J (op W)) := by
  have hab : a * b ∈ nonZeroDivisors Γ(X, W) := mul_mem ha hb
  have hIJ : (I * J).sectionsIdeal W = Ideal.span {a * b} := by
    rw [sectionsIdeal_mul_eq I J W hW, hIa, hJb, Ideal.span_singleton_mul_span_singleton]
  have hm : ∀ (s : I.sectionsIdeal W) (t : J.sectionsIdeal W),
      (DFunLike.coe (α := (((toModule I).val ⊗ (toModule J).val).obj (op W) :))
        (β := fun _ => (toModule (I * J)).val.obj (op W))
        (mulApp I J (op W)).hom (s ⊗ₜ[Γ(X, W)] t)) =
        genEquiv (I * J) (a * b) hab hIJ
          ((genEquiv I a ha hIa).symm s * (genEquiv J b hb hJb).symm t) := by
    intro s t
    apply Subtype.ext
    erw [mulApp_tmul]
    rw [genEquiv_apply_coe]
    conv_lhs => rw [← genEquiv_symm_smul I a ha hIa s, ← genEquiv_symm_smul J b hb hJb t]
    change ((genEquiv I a ha hIa).symm s * (1 * a)) * ((genEquiv J b hb hJb).symm t * (1 * b)) = _
    ring
  let ψ : (I * J).sectionsIdeal W →ₗ[Γ(X, W)]
      ((toModule I).val.obj (op W) ⊗[Γ(X, W)] (toModule J).val.obj (op W)) :=
    (LinearMap.toSpanSingleton _ _
      (genEquiv I a ha hIa 1 ⊗ₜ[Γ(X, W)] genEquiv J b hb hJb 1)).comp
      (genEquiv (I * J) (a * b) hab hIJ).symm.toLinearMap
  refine Function.bijective_iff_has_inverse.2 ⟨ψ, fun z => ?_, fun u => ?_⟩
  · induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
    | tmul s t =>
      erw [hm]
      change ((genEquiv (I * J) (a * b) hab hIJ).symm (genEquiv (I * J) (a * b) hab hIJ
          ((genEquiv I a ha hIa).symm s * (genEquiv J b hb hJb).symm t))) •
        (genEquiv I a ha hIa 1 ⊗ₜ[Γ(X, W)] genEquiv J b hb hJb 1) = s ⊗ₜ[Γ(X, W)] t
      rw [LinearEquiv.symm_apply_apply, ← TensorProduct.smul_tmul_smul,
        genEquiv_symm_smul, genEquiv_symm_smul]
  · change (DFunLike.coe (α := (((toModule I).val ⊗ (toModule J).val).obj (op W) :))
        (β := fun _ => (toModule (I * J)).val.obj (op W))
        (mulApp I J (op W)).hom (((genEquiv (I * J) (a * b) hab hIJ).symm u) •
          (genEquiv I a ha hIa 1 ⊗ₜ[Γ(X, W)] genEquiv J b hb hJb 1))) = u
    rw [LinearMap.map_smul]
    erw [hm]
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, mul_one, genEquiv_symm_smul]

end good

section cover

variable {I J}

omit I J in

lemma map_mem_nonZeroDivisors_of_eq_basicOpen (B : X.affineOpens) (h : Γ(X, B))
    {g : Γ(X, B)} (hg : g ∈ nonZeroDivisors Γ(X, B)) (W : X.Opens) (e : W = X.basicOpen h) :
    X.presheaf.map (homOfLE (e.trans_le (X.basicOpen_le h))).op g ∈ nonZeroDivisors Γ(X, W) := by
  subst e
  letI := B.2.isLocalization_basicOpen h
  exact IsLocalization.nonZeroDivisors_le_comap (M := .powers h) (S := Γ(X, X.basicOpen h)) hg

lemma sectionsIdeal_eq_span_map (K : X.IdealSheafData) (B : X.affineOpens) (g : Γ(X, B))
    (hKg : K.ideal B = Ideal.span {g}) (W : X.Opens) (hW : IsAffineOpen W) (h : W ≤ (B : X.Opens)) :
    K.sectionsIdeal W = Ideal.span {X.presheaf.map (homOfLE h).op g} := by
  rw [K.sectionsIdeal_eq_ideal ⟨W, hW⟩, ← K.map_ideal (U := ⟨W, hW⟩) (V := B) h, hKg,
    Ideal.map_span, Set.image_singleton]
  rfl

include I J in

lemma exists_good (hI : I.IsInvertible) (hJ : J.IsInvertible) {U : X.Opens} {x : X} (hx : x ∈ U) :
    ∃ (W : X.Opens) (_ : IsAffineOpen W) (a b : Γ(X, W)), a ∈ nonZeroDivisors Γ(X, W) ∧
      b ∈ nonZeroDivisors Γ(X, W) ∧ I.sectionsIdeal W = Ideal.span {a} ∧
      J.sectionsIdeal W = Ideal.span {b} ∧ x ∈ W ∧ W ≤ U := by
  obtain ⟨U₁, f₁, hx₁, g₁, hg₁, hI₁⟩ := hI x
  obtain ⟨U₂, f₂, hx₂, g₂, hg₂, hJ₂⟩ := hJ x

  let B₁ : X.affineOpens := X.affineBasicOpen f₁
  let B₂ : X.affineOpens := X.affineBasicOpen f₂

  obtain ⟨h₀, hle₀, hx₀⟩ := B₁.2.exists_basicOpen_le ⟨x, (show x ∈ U ⊓ (B₂ : X.Opens) from ⟨hx, hx₂⟩)⟩ hx₁
  let D₀ : X.affineOpens := X.affineBasicOpen h₀

  obtain ⟨h, h', hhh', hxh⟩ := exists_basicOpen_le_affine_inter D₀.2 B₂.2 x ⟨hx₀, hx₂⟩
  refine ⟨X.basicOpen h, (X.affineBasicOpen h).2,
    X.presheaf.map (homOfLE ((X.basicOpen_le h).trans (X.basicOpen_le h₀))).op g₁,
    X.presheaf.map (homOfLE (hhh'.trans_le (X.basicOpen_le h'))).op g₂, ?_, ?_, ?_, ?_, hxh,
    (X.basicOpen_le h).trans (hle₀.trans inf_le_left)⟩
  ·
    have h1 : X.presheaf.map (homOfLE (X.basicOpen_le h₀)).op g₁ ∈ nonZeroDivisors Γ(X, D₀) :=
      map_mem_nonZeroDivisors_of_eq_basicOpen B₁ h₀ hg₁ _ rfl
    have h2 := map_mem_nonZeroDivisors_of_eq_basicOpen D₀ h h1 (X.basicOpen h) rfl
    have e12 : X.presheaf.map (homOfLE ((rfl : X.basicOpen h = X.basicOpen h).trans_le
        (X.basicOpen_le h))).op (X.presheaf.map (homOfLE (X.basicOpen_le h₀)).op g₁) =
        X.presheaf.map (homOfLE ((X.basicOpen_le h).trans (X.basicOpen_le h₀))).op g₁ := by
      change (X.presheaf.map _ ≫ X.presheaf.map _) g₁ = _
      rw [← X.presheaf.map_comp]
      rfl
    rw [e12] at h2
    exact h2
  · exact map_mem_nonZeroDivisors_of_eq_basicOpen B₂ h' hg₂ _ hhh'
  · exact sectionsIdeal_eq_span_map I B₁ g₁ hI₁ _ (X.affineBasicOpen h).2 _
  · exact sectionsIdeal_eq_span_map J B₂ g₂ hJ₂ _ (X.affineBasicOpen h).2 _

end cover

lemma W_mulMap (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    (Opens.grothendieckTopology X).W ((PresheafOfModules.toPresheaf _).map (mulMap I J)) := by
  have hsurj : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map (mulMap I J)) := by
    constructor
    intro U u x hx
    obtain ⟨W, hW, a, b, ha, hb, hIa, hJb, hxW, hWU⟩ := exists_good hI hJ hx
    refine ⟨W, homOfLE hWU, ?_, hxW⟩
    obtain ⟨z, hz⟩ := (mulApp_bijective hW a b ha hb hIa hJb).2
      (((toModule (I * J)).val.presheaf.map (homOfLE hWU).op) u)
    exact ⟨z, hz⟩
  have hinj : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map (mulMap I J)) := by
    constructor
    intro U z₁ z₂ h x hx
    obtain ⟨W, hW, a, b, ha, hb, hIa, hJb, hxW, hWU⟩ := exists_good hI hJ hx
    refine ⟨W, homOfLE hWU, ?_, hxW⟩
    have n₁ := ConcreteCategory.congr_hom
      (((PresheafOfModules.toPresheaf _).map (mulMap I J)).naturality (homOfLE hWU).op) z₁
    have n₂ := ConcreteCategory.congr_hom
      (((PresheafOfModules.toPresheaf _).map (mulMap I J)).naturality (homOfLE hWU).op) z₂
    simp only [ConcreteCategory.comp_apply] at n₁ n₂
    apply (mulApp_bijective hW a b ha hb hIa hJb).1
    change ((PresheafOfModules.toPresheaf _).map (mulMap I J)).app _
        (((toModule I).val ⊗ (toModule J).val).presheaf.map (homOfLE hWU).op z₁) =
      ((PresheafOfModules.toPresheaf _).map (mulMap I J)).app _
        (((toModule I).val ⊗ (toModule J).val).presheaf.map (homOfLE hWU).op z₂)
    erw [n₁, n₂, h]
  exact (Opens.grothendieckTopology X).W_of_isLocallyBijective _

scoped instance isIso_sheafify_mulMap [Fact I.IsInvertible] [Fact J.IsInvertible] :
    IsIso ((Scheme.Modules.sheafify X).map (mulMap I J)) := by
  have h : ((MorphismProperty.isomorphisms _).inverseImage
      (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)))
      (mulMap I J) := by
    rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (J := Opens.grothendieckTopology X) (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)]
    exact W_mulMap I J Fact.out Fact.out
  exact h

def toModuleTensorIso [Fact I.IsInvertible] [Fact J.IsInvertible] :
    toModule I ⊗ toModule J ≅ toModule (I * J) :=
  (Scheme.Modules.tensorIsoSheafify (toModule I) (toModule J)).symm ≪≫
    asIso ((Scheme.Modules.sheafify X).map (mulMap I J)) ≪≫
    SheafOfModules.sheafifyCounitIso X.sheaf.obj X.ringCatSheaf.property (toModule (I * J))

end AlgebraicGeometry.Scheme.IdealSheafData
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor.AlgebraicGeometry.Scheme.IdealSheafData"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor.AlgebraicGeometry"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor.AlgebraicGeometry.Scheme.IdealSheafData"

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.IdealSheafData _root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor.AlgebraicGeometry.Scheme.IdealSheafData in

theorem solution {X : AlgebraicGeometry.Scheme.{u}} {I J : X.IdealSheafData}
    (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    Nonempty ((I * J).module ≅ I.module ⊗ J.module) :=
  haveI : Fact I.IsInvertible := ⟨hI⟩
  haveI : Fact J.IsInvertible := ⟨hJ⟩
  ⟨moduleIsoToModule (I * J) ≪≫ (toModuleTensorIso I J).symm ≪≫
    ((moduleIsoToModule I).symm ⊗ᵢ (moduleIsoToModule J).symm)⟩

end S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor (solution)
