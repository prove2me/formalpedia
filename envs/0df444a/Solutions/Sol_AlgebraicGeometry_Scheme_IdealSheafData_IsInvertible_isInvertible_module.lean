-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isInvertible_module
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8dc71eb8-747d-5cff-bc0b-46655e836717

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

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme.Hom Scheme.Opens.ι_appIso Scheme.Hom.image_preimage_eq_opensRange_inf Scheme IsAffineOpen Scheme.Modules Scheme.Opens Scheme.Opens.opensRange_ι Scheme.IdealSheafData Scheme.Modules.IsInvertible Scheme.IdealSheafData.IsInvertible"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "forget ringCatSheaf Modules.pullback Hom Γ Opens.ι_appIso Hom.image_preimage_eq_opensRange_inf Modules.restrictFunctor Modules.restrictFunctorIsoPullback restrictFunctor affineBasicOpen affineOpens basicOpen Modules IdealSheafData.map_ideal Opens grothendieckTopology Opens.opensRange_ι basicOpen_le restrict PresheafOfModules IdealSheafData Modules.IsInvertible IdealSheafData.IsInvertible"
namespace IdealSheafData
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "map subscheme map_id ideal map_comp inclusion subschemeι map_ideal ker_subschemeι_app module invModule IsInvertible"
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

section restrict

variable (U : X.Opens)

omit I in
def restrictRingCatSheafHom : (U : Scheme.{u}).ringCatSheaf ⟶
    (U.ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology (U : Scheme.{u})) (Opens.grothendieckTopology X)).obj
        X.ringCatSheaf :=
  ⟨𝟙 _⟩

omit I in
def restrictFunctor' : X.Modules ⥤ (U : Scheme.{u}).Modules :=
  SheafOfModules.pushforward (restrictRingCatSheafHom U)

omit I in
lemma restrictFunctor'_eq : restrictFunctor' U = Modules.restrictFunctor U.ι := by
  dsimp only [restrictFunctor', Modules.restrictFunctor, restrictRingCatSheafHom]
  congr 2
  ext V : 2
  change 𝟙 _ = (forget₂ CommRingCat RingCat).map (U.ι.appIso V.unop).inv
  rw [Scheme.Opens.ι_appIso]
  rfl

omit I in
def restrictFunctor'IsoPullback : restrictFunctor' U ≅ Modules.pullback U.ι :=
  eqToIso (restrictFunctor'_eq U) ≪≫ Modules.restrictFunctorIsoPullback U.ι

omit I in
variable {U} in
lemma image_preimage_of_le {V : X.Opens} (h : V ≤ U) : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr h

omit I in
lemma image_le (W : (U : Scheme.{u}).Opens) : U.ι ''ᵁ W ≤ U :=
  (U.ι.image_le_opensRange W).trans_eq U.opensRange_ι

omit I in

abbrev secX (W : (U : Scheme.{u}).Opens) (a : Γ(U, W)) : Γ(X, U.ι ''ᵁ W) := a

end restrict

section trivialization

variable (B : X.affineOpens) (g : Γ(X, B)) (hg : g ∈ nonZeroDivisors Γ(X, B))
  (hIg : I.ideal B = Ideal.span {g})

omit I in

def gOn (W : X.Opens) (h : W ≤ (B : X.Opens)) : Γ(X, W) := X.presheaf.map (homOfLE h).op g

omit I in
lemma gOn_res {W W' : X.Opens} (h : W ≤ (B : X.Opens)) (i : W' ⟶ W) :
    X.presheaf.map i.op (gOn B g W h) = gOn B g W' (i.le.trans h) := by
  change (X.presheaf.map _ ≫ X.presheaf.map _) g = X.presheaf.map _ g
  rw [← X.presheaf.map_comp]
  rfl

include hIg in
lemma gOn_mem (W : X.Opens) (h : W ≤ (B : X.Opens)) : gOn B g W h ∈ I.sectionsIdeal W := by
  apply I.map_mem_sectionsIdeal
  rw [sectionsIdeal_eq_ideal, hIg]
  exact Ideal.subset_span rfl

include hIg in

lemma sectionsIdeal_eq_span (W : X.Opens) (hW : IsAffineOpen W) (h : W ≤ (B : X.Opens)) :
    I.sectionsIdeal W = Ideal.span {gOn B g W h} := by
  rw [I.sectionsIdeal_eq_ideal ⟨W, hW⟩, ← I.map_ideal (U := ⟨W, hW⟩) (V := B) h, hIg,
    Ideal.map_span, Set.image_singleton]
  rfl

omit I in
include hg in

lemma gOn_mem_nonZeroDivisors (h' : Γ(X, B)) (W : X.Opens) (e : W = X.basicOpen h') :
    gOn B g W (e.trans_le (X.basicOpen_le h')) ∈ nonZeroDivisors Γ(X, W) := by
  subst e
  letI := B.2.isLocalization_basicOpen h'
  exact IsLocalization.nonZeroDivisors_le_comap (M := .powers h') (S := Γ(X, X.basicOpen h')) hg

def mulGen : SheafOfModules.unit ((B : X.Opens) : Scheme.{u}).ringCatSheaf ⟶
    (restrictFunctor' (B : X.Opens)).obj I.toModule :=
  ⟨{ app := fun W => ModuleCat.ofHom
      { toFun := fun a => (⟨secX (B : X.Opens) W.unop a * gOn B g _ (image_le _ W.unop),
          Ideal.mul_mem_left _ _ (gOn_mem I B g hIg _ _)⟩ : I.sectionsIdeal _)
        map_add' := fun a b => Subtype.ext
          (add_mul (secX (B : X.Opens) W.unop a) (secX (B : X.Opens) W.unop b) _)
        map_smul' := fun r a => Subtype.ext
          (mul_assoc (secX (B : X.Opens) W.unop r) (secX (B : X.Opens) W.unop a) _) }
     naturality := fun {W W'} i => by
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro a
       apply Subtype.ext
       show secX (B : X.Opens) W'.unop (X.presheaf.map ((B : X.Opens).ι.opensFunctor.map i.unop).op
           (secX (B : X.Opens) W.unop a)) * gOn B g _ _ =
         X.presheaf.map ((B : X.Opens).ι.opensFunctor.map i.unop).op
           (secX (B : X.Opens) W.unop a * gOn B g _ _)
       rw [map_mul, gOn_res] }⟩

lemma mulGen_app_apply_coe (W : (((B : X.Opens) : Scheme.{u}).Opens)ᵒᵖ)
    (a : Γ((B : X.Opens), W.unop)) :
    ((mulGen I B g hIg).val.app W a).1 =
      secX (B : X.Opens) W.unop a * gOn B g _ (image_le _ W.unop) := rfl

include hg in

lemma isIso_mulGen : IsIso (mulGen I B g hIg) := by
  set ψ := mulGen I B g hIg
  let J := Opens.grothendieckTopology ((B : X.Opens) : Scheme.{u})

  have refine : ∀ (W' : ((B : X.Opens) : Scheme.{u}).Opens) (y : (B : X.Opens)), y ∈ W' →
      ∃ (h' : Γ(X, B)) (W'' : ((B : X.Opens) : Scheme.{u}).Opens) (_ : W'' ⟶ W'), y ∈ W'' ∧
        (B : X.Opens).ι ''ᵁ W'' = X.basicOpen h' := by
    intro W' y hy
    have hy' : (B : X.Opens).ι.base y ∈ (B : X.Opens).ι ''ᵁ W' := ⟨y, hy, rfl⟩
    obtain ⟨h', hle, hh'⟩ := B.2.exists_basicOpen_le ⟨_, hy'⟩ (image_le _ W' hy')
    refine ⟨h', (B : X.Opens).ι ⁻¹ᵁ (X.basicOpen h'), homOfLE ?_, hh', image_preimage_of_le
      (X.basicOpen_le h')⟩
    intro z hz
    obtain ⟨z', hz', hzz'⟩ := hle hz
    rwa [← (B : X.Opens).ι.isOpenEmbedding.injective hzz']
  have hsurj : Presheaf.IsLocallySurjective J ((SheafOfModules.toSheaf _).map ψ).hom := by
    constructor
    rintro W ⟨t, ht⟩
    refine fun y hy => ?_
    obtain ⟨h', W'', i, hyW'', hW''⟩ := refine W y hy
    refine ⟨W'', i, ?_, hyW''⟩
    have haff : IsAffineOpen ((B : X.Opens).ι ''ᵁ W'') := hW'' ▸ (X.affineBasicOpen h').2
    have ht' := I.map_mem_sectionsIdeal ((B : X.Opens).ι.opensFunctor.map i) ht
    rw [sectionsIdeal_eq_span I B g hIg _ haff (image_le _ _), Ideal.mem_span_singleton'] at ht'
    obtain ⟨a, ha⟩ := ht'
    exact ⟨a, Subtype.ext ha⟩
  have hinj : Presheaf.IsLocallyInjective J ((SheafOfModules.toSheaf _).map ψ).hom := by
    constructor
    intro W a b hab
    refine fun y hy => ?_
    obtain ⟨h', W'', i, hyW'', hW''⟩ := refine W.unop y hy
    refine ⟨W'', i, ?_, hyW''⟩
    have hab' : secX (B : X.Opens) W.unop a * gOn B g _ (image_le _ W.unop) =
        secX (B : X.Opens) W.unop b * gOn B g _ (image_le _ W.unop) := congrArg Subtype.val hab
    have := congrArg (X.presheaf.map ((B : X.Opens).ι.opensFunctor.map i).op) hab'
    rw [map_mul, map_mul, gOn_res] at this
    exact (mul_cancel_right_mem_nonZeroDivisors (gOn_mem_nonZeroDivisors B g hg h' _ hW'')).1 this
  have h₁ : IsIso ((SheafOfModules.toSheaf _).map ψ) :=
    (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨hinj, hsurj⟩
  have h₂ : IsIso ((PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map ψ)) := by
    change IsIso ((sheafToPresheaf _ _).map ((SheafOfModules.toSheaf _).map ψ))
    infer_instance
  have := (SheafOfModules.fullyFaithfulForget
    (((B : X.Opens) : Scheme.{u}).ringCatSheaf)).reflectsIsomorphisms
  have h₃ := isIso_of_reflects_iso ((SheafOfModules.forget _).map ψ)
    (PresheafOfModules.toPresheaf _)
  exact isIso_of_reflects_iso ψ (SheafOfModules.forget _)

end trivialization

end AlgebraicGeometry.Scheme.IdealSheafData
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module.AlgebraicGeometry.Scheme.IdealSheafData"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module.AlgebraicGeometry"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module.AlgebraicGeometry.Scheme.IdealSheafData"

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.IdealSheafData _root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module.AlgebraicGeometry.Scheme.IdealSheafData in

theorem solution {X : AlgebraicGeometry.Scheme.{u}} {I : X.IdealSheafData} (hI : I.IsInvertible) :
    AlgebraicGeometry.Scheme.Modules.IsInvertible I.module := by
  have h1 : Scheme.Modules.IsInvertible I.toModule := by
    refine ⟨fun x => ?_⟩
    obtain ⟨U, f, hxf, g, hg, hIg⟩ := hI x
    haveI := isIso_mulGen I (X.affineBasicOpen f) g hg hIg
    exact ⟨X.basicOpen f, hxf, ⟨(restrictFunctor'IsoPullback (X.basicOpen f)).symm.app _ ≪≫
      (asIso (mulGen I (X.affineBasicOpen f) g hIg)).symm⟩⟩
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, ⟨e⟩⟩ := h1.1 x
  exact ⟨U, hxU, ⟨(Scheme.Modules.pullback U.ι).mapIso (moduleIsoToModule I) ≪≫ e⟩⟩

end S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module (solution)
