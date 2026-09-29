-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/2e568834-7e24-55b8-aea5-5a23b1613e96

import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.RingTheory.LocalProperties.Submodule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite"

noncomputable section

namespace ZeroSchemeLoc

p2m_open "AlgebraicGeometry AlgebraicGeometry.Scheme.Modules"

variable {X : Scheme.{u}} {M : X.Modules} (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens)

def sAt (V : (U : Scheme.{u}).Opens) : Γ(M, U.ι ''ᵁ V) :=
  s.app (U.ι ''ᵁ V) (toUnitSection (U.ι ''ᵁ V) 1)

lemma sAt_top : sAt s U ⊤ = restrictSection s U := rfl

lemma unit_map_one {W W' : X.Opens} (i : W' ⟶ W) :
    (𝟙_ X.Modules).presheaf.map i.op (toUnitSection W 1) = toUnitSection W' 1 :=
  ofUnitSection_injective W' (by rw [ofUnitSection_map]; exact map_one _)

lemma map_sAt {V V' : (U : Scheme.{u}).Opens} (i : V' ⟶ V) :
    M.presheaf.map (U.ι.opensFunctor.map i).op (sAt s U V) = sAt s U V' := by
  unfold sAt
  have nat := congrArg (fun g => g (toUnitSection (U.ι ''ᵁ V) 1))
    (s.mapPresheaf.naturality (U.ι.opensFunctor.map i).op)
  simp only [Scheme.Modules.mapPresheaf_app, Opposite.unop_op, ConcreteCategory.comp_apply] at nat
  rw [← nat, unit_map_one]

lemma restrict_smul (V : (U : Scheme.{u}).Opens) (r : Γ((U : Scheme.{u}), V))
    (m : Γ(M.restrict U.ι, V)) :
    r • m = (id r : Γ(X, U.ι ''ᵁ V)) • (id m : Γ(M, U.ι ''ᵁ V)) := by
  change ((U.ι.appIso V).inv.hom r) • (id m : Γ(M, U.ι ''ᵁ V)) = _
  rw [Scheme.Opens.ι_appIso]
  rfl

variable {U} in

lemma app_smul' {N : (U : Scheme.{u}).Modules} (φ : M.restrict U.ι ⟶ N) (V : (U : Scheme.{u}).Opens)
    (r : Γ(X, U.ι ''ᵁ V)) (m : Γ(M, U.ι ''ᵁ V)) :
    φ.app V (r • m) = (id r : Γ((U : Scheme.{u}), V)) • φ.app V m := by
  have h := Scheme.Modules.Hom.app_smul φ (id r : Γ((U : Scheme.{u}), V))
    (id m : Γ(M.restrict U.ι, V))
  rw [restrict_smul] at h
  exact h

variable {U} in

def coord (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) (V : (U : Scheme.{u}).Opens)
    (m : Γ(M, U.ι ''ᵁ V)) : Γ(X, U.ι ''ᵁ V) :=
  ofUnitSection V (φ.app V m)

variable {U} in

def cf (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) (V : (U : Scheme.{u}).Opens) :
    Γ(X, U.ι ''ᵁ V) :=
  coord φ V (sAt s U V)

lemma cf_top (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) :
    U.topIso.hom.hom (cf s φ ⊤) = coeff s U φ := rfl

variable {U} in

lemma map_coord (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) {V V' : (U : Scheme.{u}).Opens}
    (i : V' ⟶ V) (m : Γ(M, U.ι ''ᵁ V)) :
    X.presheaf.map (U.ι.opensFunctor.map i).op (coord φ V m) =
      coord φ V' (M.presheaf.map (U.ι.opensFunctor.map i).op m) := by
  have nat := congrArg (fun g => g m) (φ.mapPresheaf.naturality i.op)
  simp only [Scheme.Modules.mapPresheaf_app, Opposite.unop_op, ConcreteCategory.comp_apply] at nat
  unfold coord
  change ofUnitSection V' ((𝟙_ (U : Scheme.{u}).Modules).presheaf.map i.op (φ.app V m)) = _
  exact (congrArg (ofUnitSection V') nat).symm

variable {U} in
lemma map_cf (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) {V V' : (U : Scheme.{u}).Opens}
    (i : V' ⟶ V) : X.presheaf.map (U.ι.opensFunctor.map i).op (cf s φ V) = cf s φ V' := by
  unfold cf
  rw [map_coord, map_sAt]

variable {U} in

lemma coord_smul (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) (V : (U : Scheme.{u}).Opens)
    (r : Γ(X, U.ι ''ᵁ V)) (m : Γ(M, U.ι ''ᵁ V)) :
    coord φ V (r • m) = r * coord φ V m := by
  unfold coord
  rw [app_smul']
  rfl

variable {U} in

def gen (τ : M.restrict U.ι ≅ 𝟙_ (U : Scheme.{u}).Modules) (V : (U : Scheme.{u}).Opens) :
    Γ(M, U.ι ''ᵁ V) :=
  τ.inv.app V (toUnitSection V 1)

variable {U} in

lemma coord_smul_gen (τ : M.restrict U.ι ≅ 𝟙_ (U : Scheme.{u}).Modules) (V : (U : Scheme.{u}).Opens)
    (m : Γ(M, U.ι ''ᵁ V)) : coord τ.hom V m • gen τ V = m := by
  have h1 : (id (coord τ.hom V m) : Γ((U : Scheme.{u}), V)) • toUnitSection V 1 = τ.hom.app V m :=
    congrArg (toUnitSection V) (mul_one (ofUnitSection V (τ.hom.app V m)))
  have h2 := Scheme.Modules.Hom.app_smul τ.inv (id (coord τ.hom V m) : Γ((U : Scheme.{u}), V))
    (toUnitSection V 1)
  rw [restrict_smul, h1] at h2
  have h3 := congrArg (fun g => Scheme.Modules.Hom.app g V m) τ.hom_inv_id
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at h3
  change τ.inv.app V (τ.hom.app V m) = m at h3
  rw [h3] at h2
  exact h2.symm

variable {U} in

lemma cf_eq_mul (τ : M.restrict U.ι ≅ 𝟙_ (U : Scheme.{u}).Modules)
    (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) (V : (U : Scheme.{u}).Opens) :
    cf s φ V = cf s τ.hom V * coord φ V (gen τ V) := by
  unfold cf
  conv_lhs => rw [← coord_smul_gen τ V (sAt s U V)]
  exact coord_smul φ V _ _

variable {U}

lemma image_preimage_eq_of_le {W : X.Opens} (hW : W ≤ U) : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr hW

def resX {W : X.Opens} (hW : W ≤ U) : Γ(X, U.ι ''ᵁ (U.ι ⁻¹ᵁ W)) ⟶ Γ(X, W) :=
  X.presheaf.map (homOfLE (image_preimage_eq_of_le hW).ge).op

def resX' {W : X.Opens} (hW : W ≤ U) : Γ(X, W) ⟶ Γ(X, U.ι ''ᵁ (U.ι ⁻¹ᵁ W)) :=
  X.presheaf.map (homOfLE (image_preimage_eq_of_le hW).le).op

def resM {W : X.Opens} (hW : W ≤ U) : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ W)) ⟶ Γ(M, W) :=
  M.presheaf.map (homOfLE (image_preimage_eq_of_le hW).ge).op

def resM' {W : X.Opens} (hW : W ≤ U) : Γ(M, W) ⟶ Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ W)) :=
  M.presheaf.map (homOfLE (image_preimage_eq_of_le hW).le).op

omit s in
lemma resX_resX' {W : X.Opens} (hW : W ≤ U) (r : Γ(X, W)) : resX hW (resX' hW r) = r := by
  unfold resX resX'
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    Subsingleton.elim (homOfLE _ ≫ homOfLE _) (𝟙 _), op_id, CategoryTheory.Functor.map_id]
  rfl

omit s in
lemma resX'_resX {W : X.Opens} (hW : W ≤ U) (r : Γ(X, U.ι ''ᵁ (U.ι ⁻¹ᵁ W))) :
    resX' hW (resX hW r) = r := by
  unfold resX resX'
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    Subsingleton.elim (homOfLE _ ≫ homOfLE _) (𝟙 _), op_id, CategoryTheory.Functor.map_id]
  rfl

omit s in
lemma resM_resM' {W : X.Opens} (hW : W ≤ U) (m : Γ(M, W)) : resM (M := M) hW (resM' hW m) = m := by
  unfold resM resM'
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    Subsingleton.elim (homOfLE _ ≫ homOfLE _) (𝟙 _), op_id, CategoryTheory.Functor.map_id]
  rfl

omit s in
lemma resM_smul {W : X.Opens} (hW : W ≤ U) (r : Γ(X, U.ι ''ᵁ (U.ι ⁻¹ᵁ W)))
    (m : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ W))) : resM (M := M) hW (r • m) = resX hW r • resM hW m :=
  Scheme.Modules.map_smul M _ r m

omit s in
lemma resM'_smul {W : X.Opens} (hW : W ≤ U) (r : Γ(X, W)) (m : Γ(M, W)) :
    resM' (M := M) (U := U) hW (r • m) = resX' hW r • resM' hW m :=
  Scheme.Modules.map_smul M _ r m

lemma resM'_sApp {W : X.Opens} (hW : W ≤ U) :
    resM' (U := U) hW (s.app W (toUnitSection W 1)) = sAt s U (U.ι ⁻¹ᵁ W) := by
  unfold resM' sAt
  have nat := congrArg (fun g => g (toUnitSection W 1))
    (s.mapPresheaf.naturality (homOfLE (image_preimage_eq_of_le hW).le).op)
  simp only [Scheme.Modules.mapPresheaf_app, Opposite.unop_op, ConcreteCategory.comp_apply] at nat
  rw [← nat, unit_map_one]

def cX (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) {W : X.Opens} (hW : W ≤ U) : Γ(X, W) :=
  resX hW (cf s φ (U.ι ⁻¹ᵁ W))

def tX (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) {W : X.Opens} (hW : W ≤ U)
    (m : Γ(M, W)) : Γ(X, W) :=
  resX hW (coord φ (U.ι ⁻¹ᵁ W) (resM' hW m))

def eX (τ : M.restrict U.ι ≅ 𝟙_ (U : Scheme.{u}).Modules) {W : X.Opens} (hW : W ≤ U) : Γ(M, W) :=
  resM hW (gen τ (U.ι ⁻¹ᵁ W))

lemma tX_sApp (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) {W : X.Opens} (hW : W ≤ U) :
    tX φ hW (s.app W (toUnitSection W 1)) = cX s φ hW := by
  unfold tX cX cf
  rw [resM'_sApp]

omit s in
lemma tX_smul (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) {W : X.Opens} (hW : W ≤ U)
    (r : Γ(X, W)) (m : Γ(M, W)) : tX φ hW (r • m) = r * tX φ hW m := by
  unfold tX
  rw [resM'_smul, coord_smul, map_mul, resX_resX']

omit s in
lemma tX_smul_eX (τ : M.restrict U.ι ≅ 𝟙_ (U : Scheme.{u}).Modules) {W : X.Opens} (hW : W ≤ U)
    (m : Γ(M, W)) : tX τ.hom hW m • eX τ hW = m := by
  unfold tX eX
  rw [← resM_smul]
  exact (congrArg (resM hW) (coord_smul_gen τ (U.ι ⁻¹ᵁ W) (resM' hW m))).trans (resM_resM' hW m)

lemma cX_dvd (τ : M.restrict U.ι ≅ 𝟙_ (U : Scheme.{u}).Modules) {W : X.Opens} (hW : W ≤ U)
    (t : Γ(M, W) → Γ(X, W)) (ht : ∀ (r : Γ(X, W)) (m : Γ(M, W)), t (r • m) = r * t m) :
    cX s τ.hom hW ∣ t (s.app W (toUnitSection W 1)) := by
  refine ⟨t (eX τ hW), ?_⟩
  conv_lhs => rw [← tX_smul_eX τ hW (s.app W (toUnitSection W 1))]
  rw [ht, tX_sApp]

lemma map_cX (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) {W W' : X.Opens} (hW : W ≤ U)
    (h : W' ≤ W) : X.presheaf.map (homOfLE h).op (cX s φ hW) = cX s φ (h.trans hW) := by
  unfold cX resX
  have hi : U.ι ⁻¹ᵁ W' ≤ U.ι ⁻¹ᵁ W := fun x hx => h hx
  rw [← map_cf s φ (homOfLE hi), ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← Functor.map_comp]
  exact congrFun (congrArg (fun k => ⇑(ConcreteCategory.hom (X.presheaf.map k)))
    (Subsingleton.elim _ _)) _

lemma cX_image (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) (V : (U : Scheme.{u}).Opens)
    (h : U.ι ''ᵁ V ≤ U) : cX s φ h = cf s φ V := by
  unfold cX resX
  have hi : V ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ V) := (U.ι.preimage_image_eq V).ge
  rw [← map_cf s φ (homOfLE hi)]
  exact congrFun (congrArg (fun k => ⇑(ConcreteCategory.hom (X.presheaf.map k)))
    (Subsingleton.elim _ _)) _

omit s in

theorem mem_ideal_of_forall_exists_basicOpen {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (Ω : Y.affineOpens) (r : Γ(Y, Ω.1))
    (h : ∀ y ∈ Ω.1, ∃ g : Γ(Y, Ω.1), y ∈ Y.basicOpen g ∧
      Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op r ∈ I.ideal (Y.affineBasicOpen g)) :
    r ∈ I.ideal Ω := by
  classical
  let S : Set Γ(Y, Ω.1) :=
    {g | Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op r ∈ I.ideal (Y.affineBasicOpen g)}
  have hcov : Ω.1 ≤ ⨆ g : S, Y.basicOpen g.1 := fun y hy => by
    obtain ⟨g, hyg, hg⟩ := h y hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, hg⟩, hyg⟩
  have hspan : Ideal.span S = ⊤ := Ω.2.self_le_iSup_basicOpen_iff.mp hcov
  haveI : ∀ g : S, IsLocalization.Away g.1 Γ(Y, Y.basicOpen g.1) :=
    fun g => Ω.2.isLocalization_basicOpen g.1
  refine Submodule.mem_of_isLocalized_span S hspan
    (fun g : S => Γ(Y, Y.basicOpen g.1))
    (fun g : S => Algebra.linearMap Γ(Y, Ω.1) Γ(Y, Y.basicOpen g.1)) (fun g => ?_)
  rw [← Submodule.restrictScalars_localized' Γ(Y, Y.basicOpen g.1), Submodule.restrictScalars_mem,
    Submodule.localized'_eq_span]
  have hg : Y.presheaf.map (homOfLE (Y.basicOpen_le g.1)).op r ∈ I.ideal (Y.affineBasicOpen g.1) :=
    g.2
  rw [← I.map_ideal_basicOpen] at hg
  exact hg

omit s in

theorem ideal_eq_of_forall_exists_basicOpen {Y : Scheme.{u}} (I₁ I₂ : Y.IdealSheafData)
    (Ω : Y.affineOpens)
    (h : ∀ y ∈ Ω.1, ∃ g : Γ(Y, Ω.1), y ∈ Y.basicOpen g ∧
      I₁.ideal (Y.affineBasicOpen g) = I₂.ideal (Y.affineBasicOpen g)) :
    I₁.ideal Ω = I₂.ideal Ω := by
  refine le_antisymm (fun r hr => ?_) (fun r hr => ?_)
  · refine mem_ideal_of_forall_exists_basicOpen I₂ Ω r fun y hy => ?_
    obtain ⟨g, hyg, hg⟩ := h y hy
    refine ⟨g, hyg, ?_⟩
    rw [← hg, ← I₁.map_ideal_basicOpen]
    exact Ideal.mem_map_of_mem _ hr
  · refine mem_ideal_of_forall_exists_basicOpen I₁ Ω r fun y hy => ?_
    obtain ⟨g, hyg, hg⟩ := h y hy
    refine ⟨g, hyg, ?_⟩
    rw [hg, ← I₂.map_ideal_basicOpen]
    exact Ideal.mem_map_of_mem _ hr

variable (M) in

def Idx : Type u := Σ U : X.affineOpens, (M.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules)

def piece (j : Idx M) : (j.1.1 : Scheme.{u}).IdealSheafData where
  ideal V := Ideal.span {(id (cf s j.2.hom V.1) : Γ((j.1.1 : Scheme.{u}), V.1))}
  map_ideal_basicOpen V f := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun x => Ideal.span ({x} : Set Γ((j.1.1 : Scheme.{u}), _)))
      (map_cf s j.2.hom (homOfLE ((j.1.1 : Scheme.{u}).basicOpen_le f)))

lemma ideal_piece (j : Idx M) (V : (j.1.1 : Scheme.{u}).affineOpens) :
    (piece s j).ideal V = Ideal.span {(id (cf s j.2.hom V.1) : Γ((j.1.1 : Scheme.{u}), V.1))} :=
  rfl

def cover (hM : Scheme.Modules.IsInvertible M) : X.OpenCover :=
  Scheme.Cover.mkOfCovers (Idx M) (fun j => (j.1.1 : Scheme.{u})) (fun j => j.1.1.ι) (fun x => by
    obtain ⟨U, hxU, -, ⟨τ⟩⟩ := hM.exists_restrict_iso (V := ⊤) (x := x) trivial
    exact ⟨⟨U, τ⟩, ⟨x, hxU⟩, rfl⟩)

lemma span_cX_eq (j j' : Idx M) {W : X.Opens} (hj : W ≤ j.1.1) (hj' : W ≤ j'.1.1) :
    Ideal.span {cX s j.2.hom hj} = Ideal.span {cX s j'.2.hom hj'} := by
  apply le_antisymm
  · refine Ideal.span_singleton_le_span_singleton.mpr ?_
    have := cX_dvd s j'.2 hj' (tX j.2.hom hj) (tX_smul j.2.hom hj)
    rwa [tX_sApp] at this
  · refine Ideal.span_singleton_le_span_singleton.mpr ?_
    have := cX_dvd s j.2 hj (tX j'.2.hom hj') (tX_smul j'.2.hom hj')
    rwa [tX_sApp] at this

lemma ideal_comap_piece (j : Idx M) {V : Scheme.{u}} (a : V ⟶ (j.1.1 : Scheme.{u}))
    {W : X.Opens} (hW : W ≤ j.1.1) (hWa : IsAffineOpen W) (Ω : V.affineOpens)
    (hΩ : (Ω : V.Opens) ≤ (a ≫ j.1.1.ι) ⁻¹ᵁ W) :
    ((piece s j).comap a).ideal Ω =
      Ideal.span {((a ≫ j.1.1.ι).appLE W Ω hΩ).hom (cX s j.2.hom hW)} := by
  have hVa : IsAffineOpen (j.1.1.ι ⁻¹ᵁ W) := hWa.preimage_of_isOpenImmersion j.1.1.ι
    (by rw [Scheme.Opens.opensRange_ι]; exact hW)
  have hΩ' : (Ω : V.Opens) ≤ a ⁻¹ᵁ (j.1.1.ι ⁻¹ᵁ W) := hΩ
  rw [Scheme.IdealSheafData.ideal_comap_of_le (piece s j) a ⟨_, hVa⟩ Ω hΩ', ideal_piece,
    Ideal.map_span, Set.image_singleton]
  refine congrArg (fun x => Ideal.span ({x} : Set Γ(V, Ω))) ?_

  rw [Scheme.Hom.comp_appLE]
  change _ = (a.appLE (j.1.1.ι ⁻¹ᵁ W) Ω hΩ').hom (resX' hW (cX s j.2.hom hW))
  unfold cX
  rw [resX'_resX]
  rfl

lemma comap_piece_eq (j j' : Idx M) {V : Scheme.{u}} (a : V ⟶ (j.1.1 : Scheme.{u}))
    (b : V ⟶ (j'.1.1 : Scheme.{u})) (hab : a ≫ j.1.1.ι = b ≫ j'.1.1.ι) :
    (piece s j).comap a = (piece s j').comap b := by
  refine Scheme.IdealSheafData.ext (funext fun Ω => ?_)
  refine ideal_eq_of_forall_exists_basicOpen _ _ Ω fun z hz => ?_

  have hzj : (a ≫ j.1.1.ι) z ∈ (j.1.1 : X.Opens) := by
    rw [Scheme.Hom.comp_apply]; exact (a z).2
  have hzj' : (a ≫ j.1.1.ι) z ∈ (j'.1.1 : X.Opens) := by
    rw [hab, Scheme.Hom.comp_apply]; exact (b z).2

  obtain ⟨_, ⟨W, hWa, rfl⟩, hzW, hWle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show (a ≫ j.1.1.ι) z ∈ (j.1.1 : X.Opens) ⊓ j'.1.1 from ⟨hzj, hzj'⟩)
      ((j.1.1 : X.Opens) ⊓ j'.1.1).isOpen
  have hWj : W ≤ j.1.1 := fun x hx => (hWle hx).1
  have hWj' : W ≤ j'.1.1 := fun x hx => (hWle hx).2

  obtain ⟨g, hgle, hzg⟩ :=
    Ω.2.exists_basicOpen_le (V := (Ω : V.Opens) ⊓ (a ≫ j.1.1.ι) ⁻¹ᵁ W) ⟨z, hz, hzW⟩ hz
  refine ⟨g, hzg, ?_⟩
  have hΩ : (V.affineBasicOpen g : V.Opens) ≤ (a ≫ j.1.1.ι) ⁻¹ᵁ W :=
    hgle.trans inf_le_right
  have hΩ' : (V.affineBasicOpen g : V.Opens) ≤ (b ≫ j'.1.1.ι) ⁻¹ᵁ W := hab ▸ hΩ
  rw [ideal_comap_piece s j a hWj hWa _ hΩ, ideal_comap_piece s j' b hWj' hWa _ hΩ']
  have key := congrArg (Ideal.map ((a ≫ j.1.1.ι).appLE W (V.affineBasicOpen g) hΩ).hom)
    (span_cX_eq s j j' hWj hWj')
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton] at key
  refine key.trans ?_
  have hc : ∀ {v₁ v₂ : V ⟶ X} (_ : v₁ = v₂) (h₁ : (V.affineBasicOpen g : V.Opens) ≤ v₁ ⁻¹ᵁ W)
      (h₂ : (V.affineBasicOpen g : V.Opens) ≤ v₂ ⁻¹ᵁ W),
      v₁.appLE W (V.affineBasicOpen g) h₁ = v₂.appLE W (V.affineBasicOpen g) h₂ := by
    rintro _ _ rfl _ _; rfl
  rw [hc hab hΩ hΩ']

lemma coeff_eq_cX (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) :
    coeff s U φ = cX s φ (le_refl U) := by
  have h : U.ι ''ᵁ ⊤ ≤ U := (Scheme.Opens.ι_image_top U).le
  rw [← map_cX s φ h (Scheme.Opens.ι_image_top U).ge, cX_image, ← cf_top, Scheme.Opens.topIso_hom]
  exact congrFun (congrArg (fun k => ⇑(ConcreteCategory.hom (X.presheaf.map k)))
    (Subsingleton.elim _ _)) _

variable (hM : Scheme.Modules.IsInvertible M)

def P : X.IdealSheafData :=
  (Scheme.IdealSheafData.exists_comap_eq_of_openCover (cover hM) (fun j => piece s j)
    (fun j j' V a b hab => comap_piece_eq s j j' a b hab)).choose

lemma P_comap (j : Idx M) : (P s hM).comap j.1.1.ι = piece s j :=
  (Scheme.IdealSheafData.exists_comap_eq_of_openCover (cover hM) (fun j => piece s j)
    (fun j j' V a b hab => comap_piece_eq s j j' a b hab)).choose_spec j

lemma ideal_P_self (W : X.affineOpens) (τ : M.restrict W.1.ι ≅ 𝟙_ (W.1 : Scheme.{u}).Modules) :
    (P s hM).ideal W = Ideal.span {cX s τ.hom (le_refl _)} := by
  haveI : IsAffine (W.1 : Scheme.{u}) := W.2
  let T : (W.1 : Scheme.{u}).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have h1 := congrArg (fun I : (W.1 : Scheme.{u}).IdealSheafData => I.ideal T)
    (P_comap s hM ⟨W, τ⟩)
  dsimp only at h1
  rw [ideal_piece, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.Opens.ι_appIso,
    Iso.refl_inv] at h1
  change Ideal.comap (RingHom.id _) _ = _ at h1
  rw [Ideal.comap_id] at h1
  have h1' : (P s hM).ideal ⟨W.1.ι ''ᵁ ⊤, T.2.image_of_isOpenImmersion _⟩ =
      Ideal.span {(cf s τ.hom ⊤ : Γ(X, W.1.ι ''ᵁ ⊤))} := h1
  have hle : (W.1 : X.Opens) ≤ W.1.ι ''ᵁ ⊤ := (Scheme.Opens.ι_image_top _).ge
  rw [← Scheme.IdealSheafData.map_ideal (P s hM) (U := W)
    (V := ⟨W.1.ι ''ᵁ ⊤, T.2.image_of_isOpenImmersion _⟩) hle, h1', Ideal.map_span,
    Set.image_singleton]
  refine congrArg (fun x => Ideal.span ({x} : Set Γ(X, W.1))) ?_
  change (X.presheaf.map (homOfLE hle).op) (cf s τ.hom ⊤) = _
  rw [← cX_image s τ.hom ⊤ (Scheme.Opens.ι_image_top _).le,
    map_cX s τ.hom (Scheme.Opens.ι_image_top _).le hle]

lemma ideal_P_of_le (W : X.affineOpens) (τ : M.restrict W.1.ι ≅ 𝟙_ (W.1 : Scheme.{u}).Modules)
    (Ω : X.affineOpens) (h : (Ω : X.Opens) ≤ W.1) :
    (P s hM).ideal Ω = Ideal.span {cX s τ.hom h} := by
  rw [← Scheme.IdealSheafData.map_ideal (P s hM) h, ideal_P_self, Ideal.map_span,
    Set.image_singleton]
  exact congrArg (fun x => Ideal.span ({x} : Set Γ(X, Ω.1))) (map_cX s τ.hom (le_refl _) h)

lemma coeffIdeal_le_P (V : X.affineOpens) : coeffIdeal s V.1 ≤ (P s hM).ideal V := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨φ, rfl⟩
  refine mem_ideal_of_forall_exists_basicOpen _ V _ fun x hx => ?_
  obtain ⟨W, hxW, hWV, ⟨τ⟩⟩ := hM.exists_restrict_iso (V := V.1) hx
  obtain ⟨g, hgW, hxg⟩ := V.2.exists_basicOpen_le ⟨x, hxW⟩ hx
  refine ⟨g, hxg, ?_⟩
  rw [ideal_P_of_le s hM W τ (X.affineBasicOpen g) hgW]
  refine Ideal.mem_span_singleton.mpr ?_
  rw [coeff_eq_cX, map_cX s φ (le_refl _) (X.basicOpen_le g)]
  have := cX_dvd s τ hgW (tX φ ((X.basicOpen_le g).trans (le_refl _))) (tX_smul φ _)
  rw [tX_sApp] at this
  exact this

lemma P_le (J : X.IdealSheafData) (hJ : ∀ U : X.affineOpens, coeffIdeal s U.1 ≤ J.ideal U) :
    P s hM ≤ J := by
  refine Scheme.IdealSheafData.le_def.mpr fun V r hr => ?_
  refine mem_ideal_of_forall_exists_basicOpen J V r fun x hx => ?_
  obtain ⟨W, hxW, hWV, ⟨τ⟩⟩ := hM.exists_restrict_iso (V := V.1) hx
  obtain ⟨g, hgW, hxg⟩ := V.2.exists_basicOpen_le ⟨x, hxW⟩ hx
  refine ⟨g, hxg, ?_⟩
  have h1 : X.presheaf.map (homOfLE (X.basicOpen_le g)).op r ∈
      (P s hM).ideal (X.affineBasicOpen g) := by
    rw [← (P s hM).map_ideal_basicOpen]
    exact Ideal.mem_map_of_mem _ hr
  rw [ideal_P_of_le s hM W τ (X.affineBasicOpen g) hgW] at h1
  refine (Ideal.span_singleton_le_iff_mem _).mpr ?_ h1

  have e : (X.presheaf.map (homOfLE hgW).op).hom (coeff s W τ.hom) = cX s τ.hom hgW := by
    rw [coeff_eq_cX]; exact map_cX s τ.hom (le_refl _) hgW
  have mem : (X.presheaf.map (homOfLE hgW).op).hom (coeff s W τ.hom) ∈
      J.ideal (X.affineBasicOpen g) := by
    rw [← Scheme.IdealSheafData.map_ideal J (U := X.affineBasicOpen g) (V := W) hgW]
    exact Ideal.mem_map_of_mem _ (hJ W (coeff_mem_coeffIdeal s W.1 τ.hom))
  rw [e] at mem
  exact mem

theorem zeroSchemeIdeal_eq_P : zeroSchemeIdeal s = P s hM :=
  zeroSchemeIdeal_eq_of_isLeast ⟨coeffIdeal_le_P s hM, fun J hJ => P_le s hM J hJ⟩

end ZeroSchemeLoc

end

theorem solution
    {X : Scheme.{u}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M) :
    (∀ V : X.affineOpens,
        Scheme.Modules.coeffIdeal s V.1 ≤ (Scheme.Modules.zeroSchemeIdeal s).ideal V) ∧
    ∀ (U : X.affineOpens) (τ : M.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules),
      (Scheme.Modules.zeroSchemeIdeal s).ideal U = Ideal.span {Scheme.Modules.coeff s U.1 τ.hom} ∧
        (Scheme.Modules.zeroSchemeIdeal s).ideal U = Scheme.Modules.coeffIdeal s U.1 := by
  rw [ZeroSchemeLoc.zeroSchemeIdeal_eq_P s hM]
  refine ⟨ZeroSchemeLoc.coeffIdeal_le_P s hM, fun U τ => ?_⟩
  have h := ZeroSchemeLoc.ideal_P_self s hM U τ
  rw [← ZeroSchemeLoc.coeff_eq_cX] at h
  refine ⟨h, le_antisymm ?_ (ZeroSchemeLoc.coeffIdeal_le_P s hM U)⟩
  rw [h]
  exact (Ideal.span_singleton_le_iff_mem _).mpr (Scheme.Modules.coeff_mem_coeffIdeal s U.1 τ.hom)

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2 (solution)
