-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_app_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/df89303a-f35e-5cd1-a4c9-96e29cbb149d

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_app_eq_smul

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_app_eq_smul.AlgebraicGeometry TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.appIso_inv_naturality Scheme.Modules.Hom.app_smul Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Scheme Scheme.Modules.restrictFunctor Scheme.Modules.Hom.id_app Scheme.Modules.isSheaf Scheme.Modules Scheme.Opens Scheme.Modules.map_smul Scheme.Opens.opensRange_ι Scheme.Modules.IsInvertible Scheme.Modules.toUnitSection Scheme.Modules.ofUnitSection Scheme.Modules.ofUnitSection_toUnitSection Scheme.Modules.ofUnitSection_injective Scheme.Modules.ofUnitSection_map Scheme.Modules.ofUnitSection_smul Scheme.Modules.restrictIsoOfLE"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.appIso_inv_naturality Modules.Hom.app_smul Hom.id_app Hom Γ Modules.Hom.comp_app Modules.Hom Hom.image_preimage_eq_opensRange_inf Modules.restrictFunctor Modules.Hom.id_app restrictFunctor Hom.comp_app Modules.isSheaf Modules Opens Modules.map_smul Opens.opensRange_ι restrict Modules.IsInvertible Modules.toUnitSection Modules.ofUnitSection Modules.ofUnitSection_toUnitSection Modules.ofUnitSection_injective Modules.ofUnitSection_map Modules.ofUnitSection_smul Modules.restrictIsoOfLE"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul presheaf Hom.comp_app Hom restrictFunctor Hom.id_app isSheaf restrict map_smul IsInvertible toUnitSection ofUnitSection ofUnitSection_toUnitSection ofUnitSection_injective ofUnitSection_map ofUnitSection_smul restrictIsoOfLE"
namespace EndScalarAux
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

lemma map_map {O₁ O₂ O₃ : X.Opens} (f : O₂ ⟶ O₁) (g : O₃ ⟶ O₂) (c : Γ(X, O₁)) :
    X.presheaf.map g.op (X.presheaf.map f.op c) = X.presheaf.map (g ≫ f).op c := by
  rw [op_comp, Functor.map_comp]; rfl

lemma map_irrel {O₁ O₂ : X.Opens} (f g : O₂ ⟶ O₁) (c : Γ(X, O₁)) :
    X.presheaf.map f.op c = X.presheaf.map g.op c := by
  rw [Subsingleton.elim f g]

lemma app_map {M N : X.Modules} (φ : M ⟶ N) {O O' : X.Opens} (i : O' ⟶ O) (s : Γ(M, O)) :
    φ.app O' (M.presheaf.map i.op s) = N.presheaf.map i.op (φ.app O s) := by
  have h := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) s
  simpa using h

def ActsBy {L : X.Modules} (γ : L ⟶ L) (O : X.Opens) (c : Γ(X, O)) : Prop :=
  ∀ s : Γ(L, O), γ.app O s = c • s

lemma ActsBy.congr {L : X.Modules} {γ : L ⟶ L} {O₁ O₂ : X.Opens} (h : O₁ = O₂) {c : Γ(X, O₁)}
    (hc : ActsBy γ O₁ c) : ActsBy γ O₂ (X.presheaf.map (eqToHom h.symm).op c) := by
  subst h
  simpa using hc

section Trivial

variable {Y : Scheme.{u}}

lemma unit_end_app (δ : 𝟙_ Y.Modules ⟶ 𝟙_ Y.Modules) (V : Y.Opens) (r : Γ(𝟙_ Y.Modules, V)) :
    δ.app V r = Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
      (Scheme.Modules.ofUnitSection ⊤ (δ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1))) • r := by

  have h1 : r = Scheme.Modules.ofUnitSection V r • Scheme.Modules.toUnitSection V 1 := by
    apply Scheme.Modules.ofUnitSection_injective V
    rw [Scheme.Modules.ofUnitSection_smul, Scheme.Modules.ofUnitSection_toUnitSection, mul_one]
  have h2 : Scheme.Modules.toUnitSection V (1 : Γ(Y, V)) =
      (𝟙_ Y.Modules).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (Scheme.Modules.toUnitSection ⊤ 1) := by
    apply Scheme.Modules.ofUnitSection_injective V
    rw [Scheme.Modules.ofUnitSection_map, Scheme.Modules.ofUnitSection_toUnitSection,
      Scheme.Modules.ofUnitSection_toUnitSection, map_one]
  conv_lhs => rw [h1, Scheme.Modules.Hom.app_smul, h2, app_map]
  apply Scheme.Modules.ofUnitSection_injective V
  rw [Scheme.Modules.ofUnitSection_smul, Scheme.Modules.ofUnitSection_smul, Scheme.Modules.ofUnitSection_map,
    mul_comm]

noncomputable def scalarOf {L' : Y.Modules} (τ : L' ≅ 𝟙_ Y.Modules) (γ' : L' ⟶ L') : Γ(Y, ⊤) :=
  Scheme.Modules.ofUnitSection ⊤ ((τ.inv ≫ γ' ≫ τ.hom).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1))

lemma trivial_end_app {L' : Y.Modules} (τ : L' ≅ 𝟙_ Y.Modules) (γ' : L' ⟶ L') (V : Y.Opens) (s : Γ(L', V)) :
    γ'.app V s = Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (scalarOf τ γ') • s := by
  have hγ : γ' = τ.hom ≫ (τ.inv ≫ γ' ≫ τ.hom) ≫ τ.inv := by simp
  conv_lhs => rw [hγ]
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app]
  change τ.inv.app V ((τ.inv ≫ γ' ≫ τ.hom).app V (τ.hom.app V s)) = _
  rw [unit_end_app, Scheme.Modules.Hom.app_smul]
  change _ • (τ.hom.app V ≫ τ.inv.app V) s = _
  rw [← Scheme.Modules.Hom.comp_app, τ.hom_inv_id, Scheme.Modules.Hom.id_app]
  rfl

lemma trivial_end_unique {L' : Y.Modules} (τ : L' ≅ 𝟙_ Y.Modules) (γ' : L' ⟶ L') (a b : Γ(Y, ⊤))
    (ha : ∀ s : Γ(L', ⊤), γ'.app ⊤ s = a • s) (hb : ∀ s : Γ(L', ⊤), γ'.app ⊤ s = b • s) : a = b := by
  let m : Γ(L', ⊤) := τ.inv.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)
  have hm : τ.hom.app ⊤ m = Scheme.Modules.toUnitSection ⊤ 1 := by
    change (τ.inv.app ⊤ ≫ τ.hom.app ⊤) _ = _
    rw [← Scheme.Modules.Hom.comp_app, τ.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl
  have h : a • m = b • m := (ha m).symm.trans (hb m)
  have h' := congrArg (fun t => Scheme.Modules.ofUnitSection ⊤ (τ.hom.app ⊤ t)) h
  simp only [Scheme.Modules.Hom.app_smul, hm, Scheme.Modules.ofUnitSection_smul,
    Scheme.Modules.ofUnitSection_toUnitSection, mul_one] at h'
  exact h'

end Trivial

section OnOpen

variable {L : X.Modules} (γ : L ⟶ L) (W : X.Opens) (τ : L.restrict W.ι ≅ 𝟙_ (W : Scheme.{u}).Modules)

noncomputable def scalarOn : Γ(X, W.ι ''ᵁ ⊤) :=
  (W.ι.appIso ⊤).inv (scalarOf τ ((Scheme.Modules.restrictFunctor W.ι).map γ))

lemma actsBy_image (V : (W : Scheme.{u}).Opens) :
    ActsBy γ (W.ι ''ᵁ V) (X.presheaf.map (homOfLE (W.ι.image_mono (le_top : V ≤ ⊤))).op (scalarOn γ W τ)) := by
  intro s
  have h := trivial_end_app τ ((Scheme.Modules.restrictFunctor W.ι).map γ) V s

  have hs : (W.ι.appIso V).inv ((W : Scheme.{u}).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
      (scalarOf τ ((Scheme.Modules.restrictFunctor W.ι).map γ))) =
      X.presheaf.map (homOfLE (W.ι.image_mono (le_top : V ≤ ⊤))).op (scalarOn γ W τ) := by
    change ((W : Scheme.{u}).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫ (W.ι.appIso V).inv) _ = _
    rw [Scheme.Hom.appIso_inv_naturality]
    change X.presheaf.map (W.ι.opensFunctor.op.map (homOfLE (le_top : V ≤ ⊤)).op) (scalarOn γ W τ) = _
    exact map_irrel _ _ _
  rw [← hs]
  exact h

lemma actsBy_of_le (O : X.Opens) (hO : O ≤ W) (c : Γ(X, O))
    (hc : c = X.presheaf.map (homOfLE (show O ≤ W.ι ''ᵁ ⊤ from W.ι_image_top.symm ▸ hO)).op (scalarOn γ W τ)) :
    ActsBy γ O c := by
  have hO' : W.ι ''ᵁ (W.ι ⁻¹ᵁ O) = O := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hO]
  have h := (actsBy_image γ W τ (W.ι ⁻¹ᵁ O)).congr hO'
  rw [map_map] at h
  rw [hc]
  exact map_irrel _ _ _ ▸ h

lemma scalar_unique (τ : L.restrict W.ι ≅ 𝟙_ (W : Scheme.{u}).Modules) (a b : Γ(X, W.ι ''ᵁ ⊤)) (ha : ActsBy γ (W.ι ''ᵁ ⊤) a) (hb : ActsBy γ (W.ι ''ᵁ ⊤) b) :
    a = b := by

  have key : (W.ι.appIso ⊤).hom a = (W.ι.appIso ⊤).hom b := by
    refine trivial_end_unique τ ((Scheme.Modules.restrictFunctor W.ι).map γ) _ _ (fun s => ?_) (fun s => ?_)
    · change γ.app (W.ι ''ᵁ ⊤) s = (W.ι.appIso ⊤).inv ((W.ι.appIso ⊤).hom a) • (show Γ(L, W.ι ''ᵁ ⊤) from s)
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id]
      exact ha s
    · change γ.app (W.ι ''ᵁ ⊤) s = (W.ι.appIso ⊤).inv ((W.ι.appIso ⊤).hom b) • (show Γ(L, W.ι ''ᵁ ⊤) from s)
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id]
      exact hb s
  have := congrArg (W.ι.appIso ⊤).inv key
  rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Iso.hom_inv_id] at this

end OnOpen

end AlgebraicGeometry.Scheme.Modules.EndScalarAux

open AlgebraicGeometry.Scheme.Modules.EndScalarAux in
theorem solution
    {X : Scheme.{u}} {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) (γ : L ⟶ L) :
    ∃ u : Γ(X, ⊤), ∀ (U : X.Opens) (s : Γ(L, U)),
      γ.app U s = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op u • s := by
  classical

  choose U₀ hxU₀ hE using hL.exists_trivialization
  let e : ∀ x : X, _ := fun x => (hE x).some

  let τ : ∀ (x : X) (O : X.Opens), O ≤ U₀ x → (L.restrict O.ι ≅ 𝟙_ (O : Scheme.{u}).Modules) :=
    fun x O h => Scheme.Modules.restrictIsoOfLE (M := L) h (e x)

  let toSelf : ∀ O : X.Opens, Γ(X, O.ι ''ᵁ ⊤) → Γ(X, O) :=
    fun O c => X.presheaf.map (eqToHom O.ι_image_top.symm).op c
  let sf : ∀ x : X, Γ(X, U₀ x) := fun x => toSelf (U₀ x) (scalarOn γ (U₀ x) (τ x (U₀ x) le_rfl))

  have hloc : ∀ (x : X) (O : X.Opens) (hO : O ≤ U₀ x),
      ActsBy γ O (X.presheaf.map (homOfLE hO).op (sf x)) := by
    intro x O hO
    refine actsBy_of_le γ (U₀ x) (τ x (U₀ x) le_rfl) O hO _ ?_
    simp only [sf, toSelf, map_map]
    exact map_irrel _ _ _

  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.val U₀ sf := by
    intro x y
    let O : X.Opens := U₀ x ⊓ U₀ y
    have hx : ActsBy γ (O.ι ''ᵁ ⊤) (X.presheaf.map (homOfLE (O.ι_image_top.le.trans inf_le_left)).op (sf x)) :=
      hloc x _ _
    have hy : ActsBy γ (O.ι ''ᵁ ⊤) (X.presheaf.map (homOfLE (O.ι_image_top.le.trans inf_le_right)).op (sf y)) :=
      hloc y _ _
    have h := scalar_unique γ O (τ x O inf_le_left) _ _ hx hy
    have h' := congrArg (toSelf O) h
    simp only [toSelf, map_map] at h'
    change X.presheaf.map _ (sf x) = X.presheaf.map _ (sf y)
    exact (map_irrel _ _ _).trans (h'.trans (map_irrel _ _ _))

  obtain ⟨u, hu, -⟩ := X.sheaf.existsUnique_gluing' U₀ ⊤ (fun x => homOfLE le_top)
    (fun x _ => Opens.mem_iSup.mpr ⟨x, hxU₀ x⟩) sf hcompat
  have hu' : ∀ x, X.presheaf.map (homOfLE (le_top : U₀ x ≤ ⊤)).op u = sf x := hu
  refine ⟨u, fun U s => ?_⟩

  let F : TopCat.Sheaf Ab X := ⟨L.presheaf, Scheme.Modules.isSheaf L⟩
  refine F.eq_of_locally_eq' (fun x => U ⊓ U₀ x) U (fun x => homOfLE inf_le_left)
    (fun y hy => Opens.mem_iSup.mpr ⟨y, ⟨hy, hxU₀ y⟩⟩) _ _ fun x => ?_
  change L.presheaf.map (homOfLE (inf_le_left : U ⊓ U₀ x ≤ U)).op (γ.app U s) =
    L.presheaf.map (homOfLE (inf_le_left : U ⊓ U₀ x ≤ U)).op (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op u • s)
  rw [← app_map, Scheme.Modules.map_smul, hloc x (U ⊓ U₀ x) inf_le_right, ← hu' x, map_map, map_map]
  exact congrArg (· • _) (map_irrel _ _ _)

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_app_eq_smul
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_app_eq_smul (solution)
