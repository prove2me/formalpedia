-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_unit_of_isOpenImmersion_of_uniqueFactorizationMonoid
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/80566644-e109-50cc-827b-3f9bc22618fa

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import Theorems.Thm_UniqueFactorizationMonoid_exists_forall_mul_eq_of_cocycle_of_injective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unitCocycle_map_eq_smul_of_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_glueOfCocycle_app_eq_glueFrame
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_glueOfCocycle_trivial_iso_tensorUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_isOpenImmersion_of_uniqueFactorizationMonoid
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry TopologicalSpace CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlueOfCocycle"

noncomputable section

namespace PicUFD

variable {B : Type u} [CommRing B] [IsDomain B] {Y : Scheme.{u}}

abbrev S (B : Type u) [CommRing B] : Scheme.{u} := Spec (CommRingCat.of B)

abbrev toΓ (b : B) : Γ(S B, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b

theorem genericPoint_mem {O : (S B).Opens} (h : (O : Set (S B)).Nonempty) : genericPoint (S B) ∈ O :=
  ((genericPoint_spec (S B)).mem_open_set_iff O.isOpen).mpr (by simpa using h)

abbrev γ (O : (S B).Opens) (h : genericPoint (S B) ∈ O) : Γ(S B, O) →+* (S B).functionField :=
  ((S B).presheaf.germ O (genericPoint (S B)) h).hom

theorem γ_injective (O : (S B).Opens) (h : genericPoint (S B) ∈ O) : Function.Injective (γ O h) :=
  germ_injective_of_isIntegral (S B) _ h

theorem γ_res {O O' : (S B).Opens} (hle : O' ≤ O) (h' : genericPoint (S B) ∈ O') (x : Γ(S B, O)) :
    γ O' h' (rO hle x) = γ O (hle h') x :=
  TopCat.Presheaf.germ_res_apply (S B).presheaf (homOfLE hle) _ h' x

abbrev ρ (g : Y ⟶ Spec (CommRingCat.of B)) [IsOpenImmersion g] (O : Y.Opens) (h : genericPoint (S B) ∈ g ''ᵁ O) : Γ(Y, O) →+* (S B).functionField :=
  (γ (g ''ᵁ O) h).comp (g.appIso O).inv.hom

theorem ρ_injective (g : Y ⟶ Spec (CommRingCat.of B)) [IsOpenImmersion g] (O : Y.Opens) (h : genericPoint (S B) ∈ g ''ᵁ O) : Function.Injective (ρ g O h) :=
  (γ_injective _ h).comp (ConcreteCategory.bijective_of_isIso (g.appIso O).inv).1

theorem ρ_res (g : Y ⟶ Spec (CommRingCat.of B)) [IsOpenImmersion g] {O O' : Y.Opens} (hle : O' ≤ O) (h' : genericPoint (S B) ∈ g ''ᵁ O') (h : genericPoint (S B) ∈ g ''ᵁ O)
    (x : Γ(Y, O)) : ρ g O' h' (rO hle x) = ρ g O h x := by
  have nat := CategoryTheory.ConcreteCategory.congr_hom (Scheme.Hom.appIso_inv_naturality g (homOfLE hle).op) x
  simp only [CategoryTheory.ConcreteCategory.comp_apply] at nat
  have nat' : (g.appIso O').inv.hom ((Y.presheaf.map (homOfLE hle).op).hom x) =
      ((S B).presheaf.map ((Scheme.Hom.opensFunctor g).op.map (homOfLE hle).op)).hom ((g.appIso O).inv.hom x) := nat
  show γ _ h' ((g.appIso O').inv.hom ((Y.presheaf.map (homOfLE hle).op).hom x)) = γ _ h ((g.appIso O).inv.hom x)
  rw [nat']
  exact TopCat.Presheaf.germ_res_apply (S B).presheaf _ _ h' _

abbrev φ (B : Type u) [CommRing B] [IsDomain B] : B →+* (S B).functionField :=
  (γ ⊤ trivial).comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom

theorem φ_injective : Function.Injective (φ B) :=
  (γ_injective ⊤ trivial).comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv).1

theorem γ_rO_top {O : (S B).Opens} (h : genericPoint (S B) ∈ O) (a : Γ(S B, ⊤)) :
    γ O h (rO le_top a) = γ ⊤ trivial a :=
  γ_res le_top h a

theorem imle (g : Y ⟶ Spec (CommRingCat.of B)) [IsOpenImmersion g] {O O' : Y.Opens} (hle : O' ≤ O) : g ''ᵁ O' ≤ g ''ᵁ O :=
  fun _ ⟨y, hy, e⟩ => ⟨y, hle hy, e⟩

theorem mem_img (g : Y ⟶ Spec (CommRingCat.of B)) [IsOpenImmersion g] {O : (S B).Opens} (hO : O ≤ Scheme.Hom.opensRange g) (hne : (O : Set (S B)).Nonempty) :
    genericPoint (S B) ∈ g ''ᵁ (g ⁻¹ᵁ O) := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hO]; exact genericPoint_mem hne

theorem img_preimage (g : Y ⟶ Spec (CommRingCat.of B)) [IsOpenImmersion g] {O : (S B).Opens} (hO : O ≤ Scheme.Hom.opensRange g) : g ''ᵁ (g ⁻¹ᵁ O) = O := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hO]

theorem map_smul' {X : Scheme.{u}} (M : X.Modules) {A' B' : X.Opens} (h : B' ≤ A') (a : Γ(X, A')) (s : Γ(M, A')) :
    M.presheaf.map (homOfLE h).op (a • s) = rO h a • M.presheaf.map (homOfLE h).op s :=
  M.val.map_smul (homOfLE h).op a s

theorem isFrameOn_smul {X : Scheme.{u}} {M : X.Modules} {A' V : X.Opens} {s : Γ(M, A')} (hs : IsFrameOn s V)
    {a : Γ(X, A')} (ha : IsUnit a) : IsFrameOn (a • s) V := by
  intro W hWU hWV
  have e1 : (fun g' : Γ(X, W) => g' • M.presheaf.map (homOfLE hWU).op (a • s)) =
      (fun g' : Γ(X, W) => g' • M.presheaf.map (homOfLE hWU).op s) ∘ (fun g' => g' * rO hWU a) := by
    funext g'; simp only [Function.comp_apply, map_smul', smul_smul]
  rw [e1]
  exact (hs hWU hWV).comp (Units.mulRight (ha.map (rO hWU)).unit).bijective

def Idx (g : Y ⟶ Spec (CommRingCat.of B)) [IsOpenImmersion g] (L : Y.Modules) : Type u :=
  {b : B // (S B).basicOpen (toΓ b) ≤ Scheme.Hom.opensRange g ∧ ((S B).basicOpen (toΓ b) : Set (S B)).Nonempty ∧
    ∃ s : Γ(L, g ⁻¹ᵁ (S B).basicOpen (toΓ b)), IsFrameOn s (g ⁻¹ᵁ (S B).basicOpen (toΓ b))}

set_option maxHeartbeats 3200000 in
theorem main [UniqueFactorizationMonoid B] (g : Y ⟶ Spec (CommRingCat.of B)) [IsOpenImmersion g] {L : Y.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (L ≅ SheafOfModules.unit Y.ringCatSheaf) := by
  classical
  let D : Idx g L → (S B).Opens := fun i => (S B).basicOpen (toΓ i.1)
  let U : Idx g L → Y.Opens := fun i => g ⁻¹ᵁ D i
  have hDr : ∀ i, D i ≤ Scheme.Hom.opensRange g := fun i => i.2.1
  have hD : ∀ i, (D i : Set (S B)).Nonempty := fun i => i.2.2.1

  have hU : ⨆ i, U i = ⊤ := by
    refine top_le_iff.mp fun y _ => ?_
    obtain ⟨O, hyO, ⟨eO⟩⟩ := hL.exists_trivialization y
    have hgy : g.base y ∈ ((g ''ᵁ O : (S B).Opens) : Set (S B)) := ⟨y, hyO, rfl⟩
    obtain ⟨_, ⟨V', ⟨f, rfl⟩, rfl⟩, hyf, hfO⟩ := (isBasis_basicOpen (S B)).exists_subset_of_mem_open hgy (g ''ᵁ O).isOpen
    let b : B := (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom f
    have hb : toΓ b = f := CategoryTheory.Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of B)) f
    obtain ⟨s, hs⟩ := exists_isFrameOn_of_pullback_iso_unit O eO
    have hle1 : (S B).basicOpen f ≤ Scheme.Hom.opensRange g := fun z hz => Scheme.Hom.image_le_opensRange g O (hfO hz)
    have hle2 : g ⁻¹ᵁ (S B).basicOpen f ≤ O := fun z hz => (Scheme.Hom.preimage_image_eq g O).le (hfO hz)
    let i : Idx g L := ⟨b, by rw [hb]; exact hle1, by rw [hb]; exact ⟨_, hyf⟩, by
      rw [hb]; exact ⟨L.presheaf.map (homOfLE hle2).op s, (hs.map (homOfLE hle2)).mono hle2⟩⟩
    refine Opens.mem_iSup.mpr ⟨i, ?_⟩
    show g.base y ∈ (S B).basicOpen (toΓ b)
    rw [hb]; exact hyf

  have hex : ∀ i : Idx g L, ∃ s : Γ(L, U i), IsFrameOn s (U i) := fun i => i.2.2.2
  choose e he using hex
  obtain ⟨c, hc⟩ := exists_unitCocycle_map_eq_smul_of_isFrameOn e he

  have mem1 : ∀ i, genericPoint (S B) ∈ g ''ᵁ U i := fun i => mem_img g (hDr i) (hD i)
  have hD2 : ∀ i j, ((D i ⊓ D j : (S B).Opens) : Set (S B)).Nonempty := fun i j =>
    nonempty_preirreducible_inter (D i).isOpen (D j).isOpen (hD i) (hD j)
  have mem2 : ∀ i j, genericPoint (S B) ∈ g ''ᵁ (U i ⊓ U j) := fun i j =>
    mem_img g (O := D i ⊓ D j) (inf_le_left.trans (hDr i)) (hD2 i j)
  have mem3 : ∀ i j k, genericPoint (S B) ∈ g ''ᵁ (U i ⊓ U j ⊓ U k) := fun i j k =>
    mem_img g (O := D i ⊓ D j ⊓ D k) ((inf_le_left.trans inf_le_left).trans (hDr i))
      (nonempty_preirreducible_inter (D i ⊓ D j).isOpen (D k).isOpen (hD2 i j) (hD k))

  let uK : Idx g L → Idx g L → (S B).functionField := fun i j => ρ g (U i ⊓ U j) (mem2 i j) (c.u i j)
  have hrefl : ∀ i : Idx g L, i.1 ≠ 0 → uK i i = 1 := fun i _ => by
    show ρ g (U i ⊓ U i) (mem2 i i) (c.u i i) = 1
    rw [c.refl, map_one]
  have hcoc : ∀ i j k : Idx g L, i.1 ≠ 0 → j.1 ≠ 0 → k.1 ≠ 0 → uK i j * uK j k = uK i k := fun i j k _ _ _ => by
    have h := congrArg (ρ g (U i ⊓ U j ⊓ U k) (mem3 i j k)) (c.cocycle i j k)
    rw [map_mul, ρ_res g _ (mem3 i j k) (mem2 i j), ρ_res g _ (mem3 i j k) (mem2 j k),
      ρ_res g _ (mem3 i j k) (mem2 i k)] at h
    exact h

  have γ_alg : ∀ (f : Γ(S B, ⊤)) (O : (S B).Opens) (hO : O ≤ ⊤) (h : genericPoint (S B) ∈ O),
      γ O h (rO hO f) = φ B ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom f) := by
    intro f O hO h
    rw [γ_res]
    show _ = γ ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom f))
    rw [CategoryTheory.Iso.hom_inv_id_apply]
  have toΓ_hom : ∀ a : Γ(S B, ⊤), toΓ ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom a) = a := fun a =>
    CategoryTheory.Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of B)) a
  have hom_toΓ : ∀ b : B, (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (toΓ b) = b := fun b =>
    CategoryTheory.Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of B)) b

  have hreg : ∀ i j : Idx g L, i.1 ≠ 0 → j.1 ≠ 0 →
      ∃ (n : ℕ) (x : B), uK i j * φ B (i.1 * j.1) ^ n = φ B x := by
    intro i j _ _
    let fij : Γ(S B, ⊤) := toΓ i.1 * toΓ j.1
    have hDij : (S B).basicOpen fij = D i ⊓ D j := (S B).basicOpen_mul _ _
    have himg : g ''ᵁ (U i ⊓ U j) = D i ⊓ D j := img_preimage g (O := D i ⊓ D j) (inf_le_left.trans (hDr i))
    have hle3 : (S B).basicOpen fij ≤ g ''ᵁ (U i ⊓ U j) := (hDij.trans himg.symm).le
    have memij : genericPoint (S B) ∈ (S B).basicOpen fij := hDij.symm ▸ genericPoint_mem (hD2 i j)
    let z : Γ(S B, g ''ᵁ (U i ⊓ U j)) := (g.appIso (U i ⊓ U j)).inv.hom (c.u i j)
    haveI hloc := (isAffineOpen_top (S B)).isLocalization_basicOpen fij
    obtain ⟨n, a, hna⟩ := IsLocalization.Away.surj fij (rO hle3 z)
    refine ⟨n, (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom a, ?_⟩
    have h := congrArg (γ ((S B).basicOpen fij) memij) hna
    rw [map_mul, map_pow, γ_res] at h

    have e1 : γ ((S B).basicOpen fij) memij (algebraMap Γ(S B, ⊤) Γ(S B, (S B).basicOpen fij) fij) = φ B (i.1 * j.1) := by
      show γ _ memij (rO ((S B).basicOpen_le fij) fij) = _
      rw [γ_alg, map_mul, hom_toΓ, hom_toΓ]
    have e2 : γ ((S B).basicOpen fij) memij (algebraMap Γ(S B, ⊤) Γ(S B, (S B).basicOpen fij) a) =
        φ B ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom a) := γ_alg a _ _ memij
    rw [e1, e2] at h
    exact h

  obtain ⟨h, hh1, hh2⟩ := UniqueFactorizationMonoid.exists_forall_mul_eq_of_cocycle_of_injective
    (φ B) φ_injective (fun i : Idx g L => i.1) uK hreg hrefl hcoc
  have hne : ∀ i : Idx g L, i.1 ≠ 0 := fun i h0 => by
    obtain ⟨z, hz⟩ := hD i
    have : D i = ⊥ := by
      show (S B).basicOpen (toΓ i.1) = ⊥
      rw [h0]
      show (S B).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom 0) = ⊥
      rw [map_zero]; exact (S B).basicOpen_zero ⊤
    rw [this] at hz; exact hz

  have hφb : ∀ i : Idx g L, φ B i.1 ≠ 0 := fun i => (map_ne_zero_iff (φ B) φ_injective).mpr (hne i)
  have lift : ∀ i : Idx g L, ∃ η : Γ(Y, U i), IsUnit η ∧ ρ g (U i) (mem1 i) η = h i := by
    intro i
    obtain ⟨hi0, ⟨n, x, hx⟩, ⟨m, y, hy⟩⟩ := hh1 i (hne i)
    let f : Γ(S B, ⊤) := toΓ i.1
    haveI hloc := (isAffineOpen_top (S B)).isLocalization_basicOpen f
    have memi : genericPoint (S B) ∈ D i := genericPoint_mem (hD i)
    let s : Γ(S B, D i) := IsLocalization.mk' Γ(S B, D i) (toΓ x) (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)
    let t : Γ(S B, D i) := IsLocalization.mk' Γ(S B, D i) (toΓ y) (⟨f ^ m, m, rfl⟩ : Submonoid.powers f)
    have hγf : γ (D i) memi (algebraMap Γ(S B, ⊤) Γ(S B, D i) f) = φ B i.1 := by
      show γ _ memi (rO ((S B).basicOpen_le f) f) = _
      rw [γ_alg, hom_toΓ]
    have hs : γ (D i) memi s = h i := by
      have sp := congrArg (γ (D i) memi) (IsLocalization.mk'_spec' Γ(S B, D i) (toΓ x) (⟨f ^ n, n, rfl⟩ : Submonoid.powers f))
      rw [map_mul] at sp
      have e3 : γ (D i) memi (algebraMap Γ(S B, ⊤) Γ(S B, D i) (↑(⟨f ^ n, n, rfl⟩ : Submonoid.powers f))) = φ B i.1 ^ n := by
        show γ _ memi (algebraMap _ _ (f ^ n)) = _
        rw [map_pow, map_pow, hγf]
      have e4 : γ (D i) memi (algebraMap Γ(S B, ⊤) Γ(S B, D i) (toΓ x)) = φ B x := by
        show γ _ memi (rO ((S B).basicOpen_le f) (toΓ x)) = _
        rw [γ_alg, hom_toΓ]
      rw [e3, e4, ← hx, mul_comm] at sp
      exact mul_right_cancel₀ (pow_ne_zero n (hφb i)) sp
    have ht : γ (D i) memi t = (h i)⁻¹ := by
      have sp := congrArg (γ (D i) memi) (IsLocalization.mk'_spec' Γ(S B, D i) (toΓ y) (⟨f ^ m, m, rfl⟩ : Submonoid.powers f))
      rw [map_mul] at sp
      have e3 : γ (D i) memi (algebraMap Γ(S B, ⊤) Γ(S B, D i) (↑(⟨f ^ m, m, rfl⟩ : Submonoid.powers f))) = φ B i.1 ^ m := by
        show γ _ memi (algebraMap _ _ (f ^ m)) = _
        rw [map_pow, map_pow, hγf]
      have e4 : γ (D i) memi (algebraMap Γ(S B, ⊤) Γ(S B, D i) (toΓ y)) = φ B y := by
        show γ _ memi (rO ((S B).basicOpen_le f) (toΓ y)) = _
        rw [γ_alg, hom_toΓ]
      rw [e3, e4, ← hy, mul_comm] at sp
      exact mul_right_cancel₀ (pow_ne_zero m (hφb i)) sp
    have hst : s * t = 1 := γ_injective (D i) memi (by rw [map_mul, hs, ht, map_one, mul_inv_cancel₀ hi0])
    have hsu : IsUnit s := isUnit_iff_exists_inv.mpr ⟨t, hst⟩
    have himg : g ''ᵁ U i = D i := img_preimage g (hDr i)
    let η : Γ(Y, U i) := (g.appIso (U i)).hom.hom (rO himg.le s)
    refine ⟨η, (hsu.map _).map _, ?_⟩
    show γ _ (mem1 i) ((g.appIso (U i)).inv.hom ((g.appIso (U i)).hom.hom (rO himg.le s))) = h i
    rw [CategoryTheory.Iso.hom_inv_id_apply, γ_res]
    exact hs
  choose η hηu hη using lift

  have he' : ∀ i, IsFrameOn (η i • e i) (U i) := fun i => isFrameOn_smul (he i) (hηu i)
  have key : ∀ i j, rO (inf_le_right : U i ⊓ U j ≤ U j) (η j) * c.u i j = rO (inf_le_left : U i ⊓ U j ≤ U i) (η i) := by
    intro i j
    apply ρ_injective g (U i ⊓ U j) (mem2 i j)
    rw [map_mul, ρ_res g _ (mem2 i j) (mem1 j), ρ_res g _ (mem2 i j) (mem1 i), hη, hη]
    show h j * uK i j = h i
    rw [mul_comm]; exact hh2 i j (hne i) (hne j)
  have htr : ∀ i j, L.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (η j • e j) =
      (UnitCocycle.trivial U).u i j • L.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (η i • e i) := by
    intro i j
    show _ = (1 : Γ(Y, U i ⊓ U j)) • _
    rw [map_smul', map_smul', hc i j, smul_smul, key, one_smul]
  obtain ⟨ψ, -⟩ := exists_iso_glueOfCocycle_app_eq_glueFrame hU (UnitCocycle.trivial U) (fun i => η i • e i) he' htr
  obtain ⟨τ, -⟩ := exists_glueOfCocycle_trivial_iso_tensorUnit (X := Y) hU
  exact ⟨ψ ≪≫ τ⟩

end PicUFD

end

theorem solution
    {B : Type u} [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of B)) [IsOpenImmersion g]
    {L : Y.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (L ≅ SheafOfModules.unit Y.ringCatSheaf) :=
  PicUFD.main g hL

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_isOpenImmersion_of_uniqueFactorizationMonoid
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_isOpenImmersion_of_uniqueFactorizationMonoid (solution)
