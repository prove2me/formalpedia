-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/9ccf3fb1-740b-57e7-84c4-0a12e015ecd9

import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.RingTheory.LocalProperties.Submodule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal

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

lemma coeff_eq_cX (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) :
    coeff s U φ = cX s φ (le_refl U) := by
  have h : U.ι ''ᵁ ⊤ ≤ U := (Scheme.Opens.ι_image_top U).le
  rw [← map_cX s φ h (Scheme.Opens.ι_image_top U).ge, cX_image, ← cf_top, Scheme.Opens.topIso_hom]
  exact congrFun (congrArg (fun k => ⇑(ConcreteCategory.hom (X.presheaf.map k)))
    (Subsingleton.elim _ _)) _

end ZeroSchemeLoc

end

noncomputable section

namespace PullSections

p2m_open "AlgebraicGeometry AlgebraicGeometry.Scheme.Modules"

variable {X X' : Scheme.{u}} (F : X' ⟶ X)

abbrev unitApp (N : X.Modules) :
    N ⟶ (Scheme.Modules.pushforward F).obj ((Scheme.Modules.pullback F).obj N) :=
  (Scheme.Modules.pullbackPushforwardAdjunction F).unit.app N

def pullSec (N : X.Modules) (U : X.Opens) (m : Γ(N, U)) :
    Γ((Scheme.Modules.pullback F).obj N, F ⁻¹ᵁ U) :=
  (unitApp F N).app U m

variable {F} in

lemma map_pullSec {N N' : X.Modules} (g : N ⟶ N') (U : X.Opens) (m : Γ(N, U)) :
    ((Scheme.Modules.pullback F).map g).app (F ⁻¹ᵁ U) (pullSec F N U m) =
      pullSec F N' U (g.app U m) := by
  have nat : g ≫ unitApp F N' =
      unitApp F N ≫ (Scheme.Modules.pushforward F).map ((Scheme.Modules.pullback F).map g) :=
    (Scheme.Modules.pullbackPushforwardAdjunction F).unit.naturality g
  have h := congrArg (fun k => Scheme.Modules.Hom.app k U m) nat
  dsimp only at h
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app] at h
  exact h.symm

lemma pullSec_map (N : X.Modules) {U V : X.Opens} (i : V ⟶ U) (m : Γ(N, U)) :
    ((Scheme.Modules.pullback F).obj N).presheaf.map
        ((TopologicalSpace.Opens.map F.base).map i).op (pullSec F N U m) =
      pullSec F N V (N.presheaf.map i.op m) := by
  have nat := congrArg (fun g => g m) ((unitApp F N).mapPresheaf.naturality i.op)
  simp only [Scheme.Modules.mapPresheaf_app, Opposite.unop_op, ConcreteCategory.comp_apply] at nat
  exact nat.symm

lemma pullSec_smul (N : X.Modules) (U : X.Opens) (r : Γ(X, U)) (m : Γ(N, U)) :
    pullSec F N U (r • m) = F.app U r • pullSec F N U m :=
  Scheme.Modules.Hom.app_smul (unitApp F N) r m

lemma pullbackUnitIso_hom_pullSec (U : X.Opens) (r : Γ(X, U)) :
    (Scheme.Modules.pullbackUnitIso F).hom.app (F ⁻¹ᵁ U)
        (pullSec F (𝟙_ X.Modules) U (toUnitSection U r)) =
      toUnitSection (F ⁻¹ᵁ U) (F.app U r) := by
  have key0 := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    F.toRingCatSheafHom
  rw [Adjunction.homEquiv_unit] at key0
  have key : unitApp F (𝟙_ X.Modules) ≫
      (Scheme.Modules.pushforward F).map (Scheme.Modules.pullbackUnitIso F).hom =
      (SheafOfModules.unitToPushforwardObjUnit F.toRingCatSheafHom :
        (𝟙_ X.Modules) ⟶ (Scheme.Modules.pushforward F).obj (𝟙_ X'.Modules)) := key0
  have h := congrArg (fun k => Scheme.Modules.Hom.app k U (toUnitSection U r)) key
  dsimp only at h
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app] at h
  exact h

lemma restrictFunctorIsoPullback_hom_app_apply {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (N : X.Modules) (U : X.Opens) (m : Γ(N, U)) :
    ((restrictFunctorIsoPullback j).hom.app N).app (j ⁻¹ᵁ U)
        (N.presheaf.map (homOfLE (j.image_preimage_le U)).op m) = pullSec j N U m := by
  have h : ((restrictAdjunction j).unit.app N :
      N ⟶ (Scheme.Modules.pushforward j).obj (N.restrict j)) ≫
      (Scheme.Modules.pushforward j).map ((restrictFunctorIsoPullback j).hom.app N) = unitApp j N :=
    Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction j)
      (Scheme.Modules.pullbackPushforwardAdjunction j) N
  exact congrArg (fun k => Scheme.Modules.Hom.app k U m) h

lemma restrictFunctorIsoPullback_inv_app_pullSec {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (N : X.Modules) (U : X.Opens) (m : Γ(N, U)) :
    ((restrictFunctorIsoPullback j).inv.app N).app (j ⁻¹ᵁ U) (pullSec j N U m) =
      N.presheaf.map (homOfLE (j.image_preimage_le U)).op m := by
  rw [← restrictFunctorIsoPullback_hom_app_apply]
  have := congrArg (fun k => Scheme.Modules.Hom.app k (j ⁻¹ᵁ U)
    (N.presheaf.map (homOfLE (j.image_preimage_le U)).op m))
    ((restrictFunctorIsoPullback j).hom_inv_id_app N)
  dsimp only at this
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at this
  exact this

lemma pullbackCongr_hom_app_pullSec {f₁ f₂ : X' ⟶ X} (e : f₁ = f₂) (N : X.Modules) (U : X.Opens)
    (m : Γ(N, U)) :
    ((pullbackCongr e).hom.app N).app (f₁ ⁻¹ᵁ U) (pullSec f₁ N U m) =
      ((Scheme.Modules.pullback f₂).obj N).presheaf.map
        (eqToHom (show f₁ ⁻¹ᵁ U = f₂ ⁻¹ᵁ U by rw [e])).op (pullSec f₂ N U m) := by
  subst e
  simp only [eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  rfl

lemma pullbackComp_inv_app_pullSec {Y : Scheme.{u}} (f : X' ⟶ Y) (g : Y ⟶ X) (N : X.Modules)
    (U : X.Opens) (m : Γ(N, U)) :
    ((pullbackComp f g).inv.app N).app ((f ≫ g) ⁻¹ᵁ U) (pullSec (f ≫ g) N U m) =
      pullSec f ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ U) (pullSec g N U m) := by
  have h0 := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv N
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h0
  have h : ((unitApp g N ≫ (Scheme.Modules.pushforward g).map
      (unitApp f ((Scheme.Modules.pullback g).obj N))) ≫
      (pushforwardComp f g).hom.app
        ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N)) :
        N ⟶ (Scheme.Modules.pushforward (f ≫ g)).obj _) =
      unitApp (f ≫ g) N ≫ (Scheme.Modules.pushforward (f ≫ g)).map ((pullbackComp f g).inv.app N) :=
    h0
  exact (congrArg (fun k => Scheme.Modules.Hom.app k U m) h).symm

lemma pullbackComp_hom_app_pullSec {Y : Scheme.{u}} (f : X' ⟶ Y) (g : Y ⟶ X) (N : X.Modules)
    (U : X.Opens) (m : Γ(N, U)) :
    ((pullbackComp f g).hom.app N).app ((f ≫ g) ⁻¹ᵁ U)
        (pullSec f ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ U) (pullSec g N U m)) =
      pullSec (f ≫ g) N U m := by
  rw [← pullbackComp_inv_app_pullSec]
  have := congrArg (fun k => Scheme.Modules.Hom.app k ((f ≫ g) ⁻¹ᵁ U) (pullSec (f ≫ g) N U m))
    ((pullbackComp f g).inv_hom_id_app N)
  dsimp only at this
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at this
  exact this

end PullSections

end

noncomputable section

namespace ZeroSchemeBC

p2m_open "AlgebraicGeometry AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal.PullSections P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal.ZeroSchemeLoc"

variable {X X' : Scheme.{u}} (F : X' ⟶ X) {M : X.Modules} (s : 𝟙_ X.Modules ⟶ M)

lemma app_map {Y : Scheme.{u}} {N N' : Y.Modules} (φ : N ⟶ N') {W₁ W₂ : Y.Opens} (i : W₁ ⟶ W₂)
    (x : Γ(N, W₂)) : φ.app W₁ (N.presheaf.map i.op x) = N'.presheaf.map i.op (φ.app W₂ x) := by
  have nat := congrArg (fun g => g x) (φ.mapPresheaf.naturality i.op)
  simp only [Scheme.Modules.mapPresheaf_app, Opposite.unop_op, ConcreteCategory.comp_apply] at nat
  exact nat

lemma inv_app_hom_app {Y : Scheme.{u}} {N N' : Y.Modules} (e : N ≅ N') (W : Y.Opens) (x : Γ(N, W)) :
    e.inv.app W (e.hom.app W x) = x := by
  have := congrArg (fun k => Scheme.Modules.Hom.app k W x) e.hom_inv_id
  dsimp only at this
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at this
  exact this

lemma pullbackSection_app (U : X.Opens) :
    (pullbackSection F s).app (F ⁻¹ᵁ U) (toUnitSection (F ⁻¹ᵁ U) 1) =
      pullSec F M U (s.app U (toUnitSection U 1)) := by
  have h1 : (Scheme.Modules.pullbackUnitIso F).hom.app (F ⁻¹ᵁ U)
      (pullSec F (𝟙_ X.Modules) U (toUnitSection U 1)) = toUnitSection (F ⁻¹ᵁ U) 1 := by
    rw [pullbackUnitIso_hom_pullSec, map_one]
  have h2 : (Scheme.Modules.pullbackUnitIso F).inv.app (F ⁻¹ᵁ U) (toUnitSection (F ⁻¹ᵁ U) 1) =
      pullSec F (𝟙_ X.Modules) U (toUnitSection U 1) := by
    rw [← h1, inv_app_hom_app]
  change ((Scheme.Modules.pullbackUnitIso F).inv ≫ (Scheme.Modules.pullback F).map s).app (F ⁻¹ᵁ U)
    (toUnitSection (F ⁻¹ᵁ U) 1) = _
  rw [Scheme.Modules.Hom.comp_app]
  change ((Scheme.Modules.pullback F).map s).app (F ⁻¹ᵁ U)
    ((Scheme.Modules.pullbackUnitIso F).inv.app (F ⁻¹ᵁ U) (toUnitSection (F ⁻¹ᵁ U) 1)) = _
  rw [h2, map_pullSec]

lemma G_comp {U : X.Opens} {Ω : X'.Opens} (hΩ : Ω ≤ F ⁻¹ᵁ U) :
    F.resLE U Ω hΩ ≫ U.ι = Ω.ι ≫ F := Scheme.Hom.resLE_comp_ι F hΩ

def triv {U : X.Opens} (τ : M.restrict U.ι ≅ 𝟙_ (U : Scheme.{u}).Modules) {Ω : X'.Opens}
    (hΩ : Ω ≤ F ⁻¹ᵁ U) :
    ((Scheme.Modules.pullback F).obj M).restrict Ω.ι ≅ 𝟙_ (Ω : Scheme.{u}).Modules :=
  (restrictFunctorIsoPullback Ω.ι).app _ ≪≫
  (pullbackComp Ω.ι F).app M ≪≫
  (pullbackCongr (G_comp F hΩ).symm).app M ≪≫
  ((pullbackComp (F.resLE U Ω hΩ) U.ι).app M).symm ≪≫
  (Scheme.Modules.pullback (F.resLE U Ω hΩ)).mapIso
    (((restrictFunctorIsoPullback U.ι).app M).symm ≪≫ τ) ≪≫
  Scheme.Modules.pullbackUnitIso (F.resLE U Ω hΩ)

lemma V₀_eq {U : X.Opens} {Ω : X'.Opens} (hΩ : Ω ≤ F ⁻¹ᵁ U) :
    (Ω.ι ≫ F) ⁻¹ᵁ U = (F.resLE U Ω hΩ ≫ U.ι) ⁻¹ᵁ U := by
  rw [G_comp]

lemma app_triv_sAt {U : X.Opens} (τ : M.restrict U.ι ≅ 𝟙_ (U : Scheme.{u}).Modules)
    {Ω : X'.Opens} (hΩ : Ω ≤ F ⁻¹ᵁ U) :
    (triv F τ hΩ).hom.app ((Ω.ι ≫ F) ⁻¹ᵁ U) (sAt (pullbackSection F s) Ω ((Ω.ι ≫ F) ⁻¹ᵁ U)) =
      (𝟙_ (Ω : Scheme.{u}).Modules).presheaf.map (eqToHom (V₀_eq F hΩ)).op
        (toUnitSection ((F.resLE U Ω hΩ) ⁻¹ᵁ (U.ι ⁻¹ᵁ U))
          ((F.resLE U Ω hΩ).app (U.ι ⁻¹ᵁ U) (cf s τ.hom (U.ι ⁻¹ᵁ U)))) := by
  set sU := s.app U (toUnitSection U 1) with hsU

  have hin : sAt (pullbackSection F s) Ω ((Ω.ι ≫ F) ⁻¹ᵁ U) =
      ((Scheme.Modules.pullback F).obj M).presheaf.map
        (homOfLE (Ω.ι.image_preimage_le (F ⁻¹ᵁ U))).op (pullSec F M U sU) := by
    rw [← pullbackSection_app]
    unfold sAt
    have nat := congrArg (fun g => g (toUnitSection (F ⁻¹ᵁ U) 1))
      ((pullbackSection F s).mapPresheaf.naturality
        (homOfLE (Ω.ι.image_preimage_le (F ⁻¹ᵁ U))).op)
    simp only [Scheme.Modules.mapPresheaf_app, Opposite.unop_op, ConcreteCategory.comp_apply] at nat
    rw [← nat, unit_map_one]
    rfl
  rw [hin]
  unfold triv
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.trans_hom,
    Scheme.Modules.Hom.comp_app]
  change (Scheme.Modules.pullbackUnitIso (F.resLE U Ω hΩ)).hom.app _
    (((Scheme.Modules.pullback (F.resLE U Ω hΩ)).map
      (((restrictFunctorIsoPullback U.ι).inv.app M) ≫ τ.hom)).app _
      (((pullbackComp (F.resLE U Ω hΩ) U.ι).inv.app M).app _
        (((pullbackCongr (G_comp F hΩ).symm).hom.app M).app ((Ω.ι ≫ F) ⁻¹ᵁ U)
          (((pullbackComp Ω.ι F).hom.app M).app ((Ω.ι ≫ F) ⁻¹ᵁ U)
            (((restrictFunctorIsoPullback Ω.ι).hom.app _).app ((Ω.ι ≫ F) ⁻¹ᵁ U)
              (((Scheme.Modules.pullback F).obj M).presheaf.map
                (homOfLE (Ω.ι.image_preimage_le (F ⁻¹ᵁ U))).op (pullSec F M U sU))))))) = _

  have hA : ((restrictFunctorIsoPullback Ω.ι).hom.app ((Scheme.Modules.pullback F).obj M)).app
      ((Ω.ι ≫ F) ⁻¹ᵁ U) (((Scheme.Modules.pullback F).obj M).presheaf.map
        (homOfLE (Ω.ι.image_preimage_le (F ⁻¹ᵁ U))).op (pullSec F M U sU)) =
      pullSec Ω.ι ((Scheme.Modules.pullback F).obj M) (F ⁻¹ᵁ U) (pullSec F M U sU) :=
    restrictFunctorIsoPullback_hom_app_apply Ω.ι _ (F ⁻¹ᵁ U) (pullSec F M U sU)
  rw [hA]

  rw [pullbackComp_hom_app_pullSec Ω.ι F M U sU]

  rw [pullbackCongr_hom_app_pullSec (G_comp F hΩ).symm M U sU]

  change ((((pullbackComp (F.resLE U Ω hΩ) U.ι).inv.app M) ≫
    ((Scheme.Modules.pullback (F.resLE U Ω hΩ)).map
      (((restrictFunctorIsoPullback U.ι).inv.app M) ≫ τ.hom)) ≫
    (Scheme.Modules.pullbackUnitIso (F.resLE U Ω hΩ)).hom).app ((Ω.ι ≫ F) ⁻¹ᵁ U)
      (((Scheme.Modules.pullback (F.resLE U Ω hΩ ≫ U.ι)).obj M).presheaf.map
        (eqToHom (show (Ω.ι ≫ F) ⁻¹ᵁ U = (F.resLE U Ω hΩ ≫ U.ι) ⁻¹ᵁ U by rw [G_comp])).op
        (pullSec (F.resLE U Ω hΩ ≫ U.ι) M U sU))) = _
  rw [app_map, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app]
  refine congrArg ((𝟙_ (Ω : Scheme.{u}).Modules).presheaf.map _) ?_
  change (Scheme.Modules.pullbackUnitIso (F.resLE U Ω hΩ)).hom.app _
    (((Scheme.Modules.pullback (F.resLE U Ω hΩ)).map
      (((restrictFunctorIsoPullback U.ι).inv.app M) ≫ τ.hom)).app _
      (((pullbackComp (F.resLE U Ω hΩ) U.ι).inv.app M).app ((F.resLE U Ω hΩ ≫ U.ι) ⁻¹ᵁ U)
        (pullSec (F.resLE U Ω hΩ ≫ U.ι) M U sU))) = _

  rw [pullbackComp_inv_app_pullSec (F.resLE U Ω hΩ) U.ι M U sU]

  change (Scheme.Modules.pullbackUnitIso (F.resLE U Ω hΩ)).hom.app ((F.resLE U Ω hΩ) ⁻¹ᵁ (U.ι ⁻¹ᵁ U))
      (((Scheme.Modules.pullback (F.resLE U Ω hΩ)).map
        (((restrictFunctorIsoPullback U.ι).inv.app M) ≫ τ.hom)).app ((F.resLE U Ω hΩ) ⁻¹ᵁ (U.ι ⁻¹ᵁ U))
        (pullSec (F.resLE U Ω hΩ) _ (U.ι ⁻¹ᵁ U) (pullSec U.ι M U sU))) = _

  rw [map_pullSec, Scheme.Modules.Hom.comp_app]
  change (Scheme.Modules.pullbackUnitIso (F.resLE U Ω hΩ)).hom.app _
      (pullSec (F.resLE U Ω hΩ) _ (U.ι ⁻¹ᵁ U)
        (τ.hom.app (U.ι ⁻¹ᵁ U)
          (((restrictFunctorIsoPullback U.ι).inv.app M).app (U.ι ⁻¹ᵁ U) (pullSec U.ι M U sU)))) = _
  rw [restrictFunctorIsoPullback_inv_app_pullSec]

  have hres : M.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op sU = sAt s U (U.ι ⁻¹ᵁ U) := by
    rw [hsU, ← resM'_sApp s (le_refl U)]
    exact congrFun (congrArg (fun k => ⇑(ConcreteCategory.hom (M.presheaf.map k)))
      (Subsingleton.elim _ _)) _
  rw [hres]
  have hτ : τ.hom.app (U.ι ⁻¹ᵁ U) (sAt s U (U.ι ⁻¹ᵁ U)) =
      toUnitSection (X := (U : Scheme.{u})) (U.ι ⁻¹ᵁ U) (cf s τ.hom (U.ι ⁻¹ᵁ U)) := rfl
  rw [hτ]

  exact pullbackUnitIso_hom_pullSec (F.resLE U Ω hΩ) (U.ι ⁻¹ᵁ U) (cf s τ.hom (U.ι ⁻¹ᵁ U))

lemma gen_eq (U : X.affineOpens) (τ : M.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules)
    (Ω : X'.affineOpens) (hΩ : (Ω : X'.Opens) ≤ F ⁻¹ᵁ (U : X.Opens)) :
    (F.appLE U Ω hΩ).hom (coeff s U.1 τ.hom) = coeff (pullbackSection F s) Ω.1 (triv F τ hΩ).hom := by

  rw [coeff_eq_cX]
  change (F.appLE U Ω hΩ).hom ((X.presheaf.map (homOfLE _).op).hom (cf s τ.hom (U.1.ι ⁻¹ᵁ U.1))) = _
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

  rw [← cf_top]
  have hi : (⊤ : (Ω.1 : Scheme.{u}).Opens) ≤ (Ω.1.ι ≫ F) ⁻¹ᵁ U.1 := fun x _ => hΩ x.2
  rw [← map_cf (pullbackSection F s) (triv F τ hΩ).hom (homOfLE hi)]
  unfold cf coord
  rw [app_triv_sAt]
  change (F.appLE _ _ _).hom (cf s τ.hom (U.1.ι ⁻¹ᵁ U.1)) =
    ((F.resLE U.1 Ω.1 hΩ).app (U.1.ι ⁻¹ᵁ U.1) ≫ X'.presheaf.map _ ≫ X'.presheaf.map _ ≫
      X'.presheaf.map _).hom (cf s τ.hom (U.1.ι ⁻¹ᵁ U.1))
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE]
  change _ = (F.appLE _ _ _ ≫ X'.presheaf.map _ ≫ X'.presheaf.map _ ≫ X'.presheaf.map _).hom
    (cf s τ.hom (U.1.ι ⁻¹ᵁ U.1))
  simp only [← Functor.map_comp]
  erw [Scheme.Hom.appLE_map]

lemma ideal_eq_of_le (hM : Scheme.Modules.IsInvertible M) (U : X.affineOpens) (τ : M.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules)
    (Ω : X'.affineOpens) (hΩ : (Ω : X'.Opens) ≤ F ⁻¹ᵁ (U : X.Opens)) :
    ((zeroSchemeIdeal s).comap F).ideal Ω = (zeroSchemeIdeal (pullbackSection F s)).ideal Ω := by
  rw [Scheme.IdealSheafData.ideal_comap_of_le _ F U Ω hΩ,
    ((hM.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq s).2 U τ).1, Ideal.map_span,
    Set.image_singleton]
  have hM' : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback F).obj M) := hM.pullback F
  rw [((hM'.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq (pullbackSection F s)).2 Ω
    (triv F τ hΩ)).1]
  exact congrArg (fun x => Ideal.span ({x} : Set Γ(X', Ω.1))) (gen_eq F s U τ Ω hΩ)

theorem comap_zeroSchemeIdeal_eq (hM : Scheme.Modules.IsInvertible M) :
    (zeroSchemeIdeal s).comap F = zeroSchemeIdeal (pullbackSection F s) := by
  refine Scheme.IdealSheafData.ext (funext fun Ω₀ => ?_)
  refine ideal_eq_of_forall_exists_basicOpen _ _ Ω₀ fun z hz => ?_
  obtain ⟨U, hzU, -, ⟨τ⟩⟩ := hM.exists_restrict_iso (V := ⊤) (x := F z) trivial
  obtain ⟨g, hgle, hzg⟩ :=
    Ω₀.2.exists_basicOpen_le (V := (Ω₀ : X'.Opens) ⊓ F ⁻¹ᵁ U.1) ⟨z, hz, hzU⟩ hz
  exact ⟨g, hzg, ideal_eq_of_le F s hM U τ (X'.affineBasicOpen g) (hgle.trans inf_le_right)⟩

end ZeroSchemeBC

end

theorem solution
    {X X' : Scheme.{u}} (F : X' ⟶ X) {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ X.Modules ⟶ M) :
    (Scheme.Modules.zeroSchemeIdeal s).comap F =
      Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection F s) :=
  ZeroSchemeBC.comap_zeroSchemeIdeal_eq F s hM

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal (solution)
