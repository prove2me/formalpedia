-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.existsUnique_app_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/877cb4ee-a451-5c5c-a57a-252e5f0328ba

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul.AlgebraicGeometry Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom Scheme.Opens.ι_appIso Scheme.Hom.image_preimage_eq_opensRange_inf Scheme Scheme.Hom.appTop Scheme.Hom.comp_appTop Scheme.Hom.naturality Scheme.Modules Scheme.Opens Scheme.Opens.ι_image_top Scheme.Opens.opensRange_ι Scheme.Modules.IsInvertible"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules.pullback Hom Γ Opens.ι_appIso Hom.image_preimage_eq_opensRange_inf Hom.appTop Hom.comp_appTop Hom.naturality Modules Opens Opens.ι_image_top Modules.map_smul Opens.opensRange_ι restrict PresheafOfModules Modules.IsInvertible"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul pushforward pullback presheaf Hom mapPresheaf_app restrictFunctorIsoPullback isSheaf pullbackPushforwardAdjunction restrict map_smul IsInvertible"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X Y : Scheme.{u}}

noncomputable abbrev unitModule (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

namespace Hom p2m_export "AlgebraicGeometry.Scheme.Modules.Hom" "app_smul mapPresheaf app" end Hom
p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.Hom" in

lemma Hom.app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : U ⟶ V) (x : Γ(M, V)) :
    φ.app U (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app V x) := by
  have h := φ.mapPresheaf.naturality i.op
  simp only [mapPresheaf_app] at h
  have h' := ConcreteCategory.congr_hom h x
  simp only [ConcreteCategory.comp_apply] at h'
  exact h'

noncomputable abbrev resTop (s : Γ(X, ⊤)) (U : X.Opens) : Γ(X, U) :=
  X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s

@[scoped simp] lemma map_resTop (s : Γ(X, ⊤)) {U V : X.Opens} (i : U ⟶ V) :
    X.presheaf.map i.op (resTop s V) = resTop s U := by
  simp only [resTop, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

@[scoped simp] lemma resTop_top (s : Γ(X, ⊤)) : resTop s ⊤ = s := by
  simp [resTop]

lemma smul_res_comm (s : Γ(X, ⊤)) (M : X.Modules) (U : X.Opens) (r : Γ(X, U)) (m : Γ(M, U)) :
    resTop s U • r • m = r • resTop s U • m := by
  rw [smul_smul, smul_smul, mul_comm]

lemma map_resTop_smul (s : Γ(X, ⊤)) (M : X.Modules) {U V : X.Opens} (i : U ⟶ V) (x : Γ(M, V)) :
    M.presheaf.map i.op (resTop s V • x) = resTop s U • M.presheaf.map i.op x := by
  rw [Modules.map_smul, map_resTop]

noncomputable def smulHom (s : Γ(X, ⊤)) (M : X.Modules) : M ⟶ M :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        (DistribSMul.toAddMonoidHom Γ(M, U.unop) (resTop s U.unop))
      naturality := fun {U V} i => by
        ext x
        exact (map_resTop_smul s M i.unop (x : Γ(M, U.unop))).symm }
    (fun U r m => smul_res_comm s M U.unop r m)⟩

@[scoped simp] lemma smulHom_app_apply (s : Γ(X, ⊤)) (M : X.Modules) (U : X.Opens) (x : Γ(M, U)) :
    (smulHom s M).app U x = resTop s U • x := rfl

@[reassoc] lemma smulHom_comp (s : Γ(X, ⊤)) {M N : X.Modules} (φ : M ⟶ N) :
    smulHom s M ≫ φ = φ ≫ smulHom s N := by
  ext U x
  change φ.app U ((smulHom s M).app U x) = (smulHom s N).app U (φ.app U x)
  rw [smulHom_app_apply, smulHom_app_apply, Hom.app_smul]

lemma smulHom_mul (s s' : Γ(X, ⊤)) (M : X.Modules) :
    smulHom (s * s') M = smulHom s' M ≫ smulHom s M := by
  ext U x
  change (smulHom (s * s') M).app U x = (smulHom s M).app U ((smulHom s' M).app U x)
  simp only [smulHom_app_apply, resTop, map_mul, mul_smul]

@[scoped simp] lemma smulHom_one (M : X.Modules) : smulHom (1 : Γ(X, ⊤)) M = 𝟙 M := by
  ext U x
  change (smulHom 1 M).app U x = x
  simp [smulHom_app_apply, resTop]

noncomputable def smulIso (s : Γ(X, ⊤)ˣ) (M : X.Modules) : M ≅ M where
  hom := smulHom (s : Γ(X, ⊤)) M
  inv := smulHom (↑s⁻¹ : Γ(X, ⊤)) M
  hom_inv_id := by rw [← smulHom_mul, Units.inv_mul, smulHom_one]
  inv_hom_id := by rw [← smulHom_mul, Units.mul_inv, smulHom_one]

noncomputable def unitOne (U : X.Opens) : Γ(unitModule X, U) := (1 : Γ(X, U))

def toΓ {U : X.Opens} (x : Γ(unitModule X, U)) : Γ(X, U) := x

lemma eq_toΓ_smul_unitOne {U : X.Opens} (x : Γ(unitModule X, U)) : x = toΓ x • unitOne U :=
  (mul_one (toΓ x)).symm

lemma map_unitOne {U V : X.Opens} (i : U ⟶ V) :
    (unitModule X).presheaf.map i.op (unitOne V) = unitOne U :=
  map_one (X.presheaf.map i.op).hom

lemma smulHom_app_top_one (u : unitModule X ⟶ unitModule X) :
    smulHom (u.app ⊤ (unitOne ⊤)) (unitModule X) = u := by
  ext U x
  change resTop (u.app ⊤ (unitOne ⊤)) U • x = u.app U x
  have h1 : u.app U (unitOne U) = resTop (u.app ⊤ (unitOne ⊤)) U := by
    have h := Hom.app_naturality u (homOfLE (le_top : U ≤ ⊤)) (unitOne ⊤)
    rw [map_unitOne] at h
    exact h
  rw [eq_toΓ_smul_unitOne x, Hom.app_smul, h1]
  change (resTop (u.app ⊤ (unitOne ⊤)) U * (toΓ x * 1) : Γ(X, U)) = toΓ x * resTop (u.app ⊤ (unitOne ⊤)) U
  ring

lemma app_top_comp_unitOne (u v : unitModule X ⟶ unitModule X) :
    toΓ ((u ≫ v).app ⊤ (unitOne ⊤)) = toΓ (u.app ⊤ (unitOne ⊤)) * toΓ (v.app ⊤ (unitOne ⊤)) := by
  conv_lhs => rw [← smulHom_app_top_one v]
  change toΓ ((smulHom (v.app ⊤ (unitOne ⊤)) (unitModule X)).app ⊤ (u.app ⊤ (unitOne ⊤))) = _
  rw [smulHom_app_apply, resTop_top]
  exact mul_comm _ _

noncomputable def unitOfAut (δ : unitModule X ≅ unitModule X) : Γ(X, ⊤)ˣ where
  val := toΓ (δ.hom.app ⊤ (unitOne ⊤))
  inv := toΓ (δ.inv.app ⊤ (unitOne ⊤))
  val_inv := by rw [← app_top_comp_unitOne, δ.hom_inv_id]; rfl
  inv_val := by rw [← app_top_comp_unitOne, δ.inv_hom_id]; rfl

lemma smulIso_unitOfAut (δ : unitModule X ≅ unitModule X) :
    smulIso (unitOfAut δ) (unitModule X) = δ := by
  ext : 1
  exact smulHom_app_top_one δ.hom

lemma resTop_appTop (f : X ⟶ Y) (s : Γ(Y, ⊤)) (U : Y.Opens) :
    resTop (f.appTop s) (f ⁻¹ᵁ U) = f.app U (resTop s U) := by
  simp only [resTop, Scheme.Hom.appTop, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

lemma pushforward_map_smulHom (f : X ⟶ Y) (s : Γ(Y, ⊤)) (P : X.Modules) :
    (pushforward f).map (smulHom (f.appTop s) P) = smulHom s ((pushforward f).obj P) := by
  ext U x
  change (smulHom (f.appTop s) P).app (f ⁻¹ᵁ U) x = resTop s U • x
  rw [smulHom_app_apply, resTop_appTop]
  rfl

lemma pullback_map_smulHom (f : X ⟶ Y) (s : Γ(Y, ⊤)) (M : Y.Modules) :
    (pullback f).map (smulHom s M) = smulHom (f.appTop s) ((pullback f).obj M) := by
  apply ((pullbackPushforwardAdjunction f).homEquiv M ((pullback f).obj M)).injective
  have h1 := (pullbackPushforwardAdjunction f).unit.naturality (smulHom s M)
  dsimp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at h1
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  erw [← h1, pushforward_map_smulHom]
  exact smulHom_comp _ _

lemma pullback_mapIso_smulIso (f : X ⟶ Y) (s : Γ(Y, ⊤)ˣ) (M : Y.Modules) :
    (pullback f).mapIso (smulIso s M) = smulIso (Units.map (f.appTop).hom.toMonoidHom s) ((pullback f).obj M) := by
  ext : 1
  exact pullback_map_smulHom f s M

lemma appTop_appTop_of_comp_eq_id {T P : Scheme.{u}} (e : T ⟶ P) (p : P ⟶ T) (h : e ≫ p = 𝟙 T) (d : Γ(T, ⊤)) :
    e.appTop (p.appTop d) = d := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  rw [h]
  simp

end AlgebraicGeometry.Scheme.Modules
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul.AlgebraicGeometry.Scheme.Modules"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom Scheme.Opens.ι_appIso Scheme.Hom.image_preimage_eq_opensRange_inf Scheme Scheme.Hom.appTop Scheme.Hom.comp_appTop Scheme.Hom.naturality Scheme.Modules Scheme.Opens Scheme.Opens.ι_image_top Scheme.Opens.opensRange_ι Scheme.Modules.IsInvertible"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules.pullback Hom Γ Opens.ι_appIso Hom.image_preimage_eq_opensRange_inf Hom.appTop Hom.comp_appTop Hom.naturality Modules Opens Opens.ι_image_top Modules.map_smul Opens.opensRange_ι restrict PresheafOfModules Modules.IsInvertible"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul pushforward pullback presheaf Hom mapPresheaf_app restrictFunctorIsoPullback isSheaf pullbackPushforwardAdjunction restrict map_smul IsInvertible"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}} (M : X.Modules) (g : M ⟶ M)

def Represents (V : X.Opens) (s : Γ(X, V)) : Prop :=
  ∀ (W : X.Opens) (h : W ≤ V) (x : Γ(M, W)), g.app W x = X.presheaf.map (homOfLE h).op s • x

variable {M g}

lemma Represents.restrict {V V' : X.Opens} (h : V' ≤ V) {s : Γ(X, V)} (hs : Represents M g V s) :
    Represents M g V' (X.presheaf.map (homOfLE h).op s) := by
  intro W hW x
  rw [hs W (hW.trans h) x, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma presheaf_map_map {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op s) =
      X.presheaf.map (homOfLE (h₂.trans h₁)).op s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma module_map_map {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(M, U)) :
    M.presheaf.map (homOfLE h₂).op (M.presheaf.map (homOfLE h₁).op x) =
      M.presheaf.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma Represents.of_cover {V : X.Opens} {ι : Type*} (Vi : ι → X.Opens) (hVi : ∀ i, Vi i ≤ V)
    (hcov : V ≤ iSup Vi) (s : Γ(X, V))
    (h : ∀ i, Represents M g (Vi i) (X.presheaf.map (homOfLE (hVi i)).op s)) : Represents M g V s := by
  intro W hW x
  have hWcov : W ≤ ⨆ i, W ⊓ Vi i := by
    rw [← inf_iSup_eq]
    exact le_inf le_rfl (hW.trans hcov)
  apply TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X) (fun i => W ⊓ Vi i) W
    (fun i => homOfLE inf_le_left) hWcov
  intro i
  change M.presheaf.map (homOfLE (inf_le_left : W ⊓ Vi i ≤ W)).op (g.app W x) =
    M.presheaf.map (homOfLE (inf_le_left : W ⊓ Vi i ≤ W)).op (X.presheaf.map (homOfLE hW).op s • x)
  rw [← Hom.app_naturality, Modules.map_smul, presheaf_map_map,
    h i (W ⊓ Vi i) inf_le_right, presheaf_map_map]

def TrivOn (M : X.Modules) (V : X.Opens) : Prop :=
  ∃ e : Γ(M, V), ∀ (W : X.Opens) (h : W ≤ V),
    Function.Bijective (fun r : Γ(X, W) => r • M.presheaf.map (homOfLE h).op e)

lemma TrivOn.restrict {V V' : X.Opens} (h : V' ≤ V) (hV : TrivOn M V) : TrivOn M V' := by
  obtain ⟨e, he⟩ := hV
  refine ⟨M.presheaf.map (homOfLE h).op e, fun W hW => ?_⟩
  simp only [module_map_map]
  exact he W (hW.trans h)

lemma exists_represents_of_trivOn {V : X.Opens} (hV : TrivOn M V) : ∃ s, Represents M g V s := by
  obtain ⟨e, he⟩ := hV
  obtain ⟨s, hs⟩ := (he V le_rfl).2 (g.app V (M.presheaf.map (homOfLE le_rfl).op e))
  refine ⟨s, fun W hW x => ?_⟩
  obtain ⟨r, rfl⟩ := (he W hW).2 x
  dsimp only
  rw [Hom.app_smul]
  have h1 : g.app W (M.presheaf.map (homOfLE hW).op e) =
      X.presheaf.map (homOfLE hW).op s • M.presheaf.map (homOfLE hW).op e := by
    have h2 := congrArg (M.presheaf.map (homOfLE hW).op) hs
    dsimp only at h2
    rw [Modules.map_smul, module_map_map, ← Hom.app_naturality, module_map_map] at h2
    exact h2.symm
  rw [h1, smul_smul, smul_smul, mul_comm]

lemma represents_unique_of_trivOn {V : X.Opens} (hV : TrivOn M V) {s s' : Γ(X, V)}
    (hs : Represents M g V s) (hs' : Represents M g V s') : s = s' := by
  obtain ⟨e, he⟩ := hV
  have h := (hs V le_rfl (M.presheaf.map (homOfLE le_rfl).op e)).symm.trans
    (hs' V le_rfl (M.presheaf.map (homOfLE le_rfl).op e))
  have h' := (he V le_rfl).1 h
  simpa using h'

lemma trivOn_of_iso (U : X.Opens) (τ : (Modules.pullback U.ι).obj M ≅ unitModule U) :
    TrivOn M (U.ι ''ᵁ ⊤) := by
  let τ' : M.restrict U.ι ≅ unitModule (U : Scheme.{u}) := (restrictFunctorIsoPullback U.ι).app M ≪≫ τ
  let e : Γ(M, U.ι ''ᵁ ⊤) := τ'.inv.app ⊤ (unitOne ⊤)
  refine ⟨e, fun W hW => ?_⟩
  obtain ⟨W', rfl⟩ : ∃ W' : (U : Scheme.{u}).Opens, W = U.ι ''ᵁ W' :=
    ⟨U.ι ⁻¹ᵁ W, by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.mpr (hW.trans_eq (Scheme.Opens.ι_image_top U))]⟩

  have key : ∀ r : Γ(X, U.ι ''ᵁ W'),
      r • M.presheaf.map (homOfLE hW).op e = τ'.inv.app W' (@id Γ(unitModule (U : Scheme.{u}), W') r) := by
    intro r
    have hr : (@id Γ(unitModule (U : Scheme.{u}), W') r) = toΓ (@id Γ(unitModule (U : Scheme.{u}), W') r) • unitOne W' :=
      eq_toΓ_smul_unitOne _
    rw [hr, Hom.app_smul]

    have hn := Hom.app_naturality τ'.inv (homOfLE (le_top : W' ≤ ⊤)) (unitOne ⊤)
    rw [map_unitOne] at hn
    rw [hn]

    change _ = ((U.ι.appIso W').inv.hom (toΓ (@id Γ(unitModule (U : Scheme.{u}), W') r))) •
      M.presheaf.map (homOfLE hW).op e
    rw [Scheme.Opens.ι_appIso]
    rfl
  have hbij : Function.Bijective (τ'.inv.app W') := ConcreteCategory.bijective_of_isIso (τ'.inv.app W')
  rw [show (fun r : Γ(X, U.ι ''ᵁ W') => r • M.presheaf.map (homOfLE hW).op e) =
      fun r => τ'.inv.app W' (@id Γ(unitModule (U : Scheme.{u}), W') r) from funext key]
  exact hbij

namespace IsInvertible p2m_export "AlgebraicGeometry.Scheme.Modules.IsInvertible" "pullback exists_trivialization" end IsInvertible
p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.IsInvertible" in

theorem IsInvertible.existsUnique_represents (hM : Scheme.Modules.IsInvertible M) (g : M ⟶ M) :
    ∃! s : Γ(X, ⊤), ∀ (U : X.Opens) (x : Γ(M, U)),
      g.app U x = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s • x := by
  choose U hxU hτ using hM.exists_trivialization
  have htriv : ∀ x, TrivOn M (U x) := fun x => by
    have h := trivOn_of_iso (M := M) (U x) (hτ x).some
    rwa [Scheme.Opens.ι_image_top] at h
  have hcov : (⊤ : X.Opens) ≤ iSup U := fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hxU y⟩
  choose s hs using fun x => exists_represents_of_trivOn (g := g) (htriv x)
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf U s := fun i j =>
    represents_unique_of_trivOn ((htriv i).restrict inf_le_left)
      ((hs i).restrict inf_le_left) ((hs j).restrict inf_le_right)
  obtain ⟨S, hS, -⟩ := X.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) hcov s hcompat
  have hS' : ∀ i, X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (S : Γ(X, ⊤)) = s i := hS
  have hrep : Represents M g ⊤ S :=
    Represents.of_cover U (fun _ => le_top) hcov S (fun i => by rw [hS' i]; exact hs i)
  refine ⟨S, fun W x => hrep W le_top x, fun S' hS' => ?_⟩
  have hrep' : Represents M g ⊤ S' := fun W hW x => hS' W x
  apply X.sheaf.eq_of_locally_eq' U ⊤ (fun i => homOfLE le_top) hcov
  intro i
  exact represents_unique_of_trivOn (htriv i) (hrep'.restrict le_top) (hrep.restrict le_top)

end AlgebraicGeometry.Scheme.Modules
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul.AlgebraicGeometry.Scheme.Modules"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul.AlgebraicGeometry.Scheme.Modules"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul.AlgebraicGeometry.Scheme.Modules"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul.AlgebraicGeometry"

theorem solution
    {X : Scheme.{u}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (g : M ⟶ M) :
    ∃! s : Γ(X, ⊤), ∀ (U : X.Opens) (x : Γ(M, U)),
      g.app U x = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s • x :=
  AlgebraicGeometry.Scheme.Modules.IsInvertible.existsUnique_represents hM g

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul (solution)
