-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_zeroSchemeIdeal_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/9e57fdbe-f2d9-5c05-b808-c3794694deca

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_existsUnique_hom_app_eq_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_genericPoint_notMem_support_zeroSchemeIdeal_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_zeroSchemeIdeal_eq
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

namespace B1Aux

variable {X : Scheme.{u}}

lemma app_map {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : V ⟶ U) (x : Γ(M, U)) :
    φ.app V (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app U x) := by
  simpa using ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) x

lemma map_toUnitSection_one {U V : X.Opens} (i : V ⟶ U) :
    (𝟙_ X.Modules).presheaf.map i.op (Scheme.Modules.toUnitSection U 1) =
      Scheme.Modules.toUnitSection V 1 := by
  apply Scheme.Modules.ofUnitSection_injective
  rw [Scheme.Modules.ofUnitSection_map, Scheme.Modules.ofUnitSection_toUnitSection,
    Scheme.Modules.ofUnitSection_toUnitSection, map_one]

lemma mod_map_map (M : X.Modules) {A B C : X.Opens} (f : B ⟶ A) (g : C ⟶ B) (k : C ⟶ A)
    (x : Γ(M, A)) :
    M.presheaf.map g.op (M.presheaf.map f.op x) = M.presheaf.map k.op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (g ≫ f) k]

lemma ring_map_map {A B C : X.Opens} (f : B ⟶ A) (g : C ⟶ B) (k : C ⟶ A) (x : Γ(X, A)) :
    X.presheaf.map g.op (X.presheaf.map f.op x) = X.presheaf.map k.op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (g ≫ f) k]

lemma mod_map_id (M : X.Modules) {A : X.Opens} (f : A ⟶ A) (x : Γ(M, A)) :
    M.presheaf.map f.op x = x := by
  rw [Subsingleton.elim f (𝟙 A), op_id, CategoryTheory.Functor.map_id]; rfl

lemma ring_map_id {A : X.Opens} (f : A ⟶ A) (x : Γ(X, A)) : X.presheaf.map f.op x = x := by
  rw [Subsingleton.elim f (𝟙 A), op_id, CategoryTheory.Functor.map_id]; rfl

lemma app_one_eq_map {M : X.Modules} (s : 𝟙_ X.Modules ⟶ M) {U W : X.Opens} (i : W ⟶ U) :
    s.app W (Scheme.Modules.toUnitSection W 1) =
      M.presheaf.map i.op (s.app U (Scheme.Modules.toUnitSection U 1)) := by
  rw [← map_toUnitSection_one i, app_map]

lemma isFrameOn_smul {M : X.Modules} {U V : X.Opens} {e : Γ(M, U)} (he : Scheme.Modules.IsFrameOn e V)
    {u : Γ(X, U)} (hu : IsUnit u) : Scheme.Modules.IsFrameOn (u • e) V := by
  intro W hWU hWV
  have hb := he hWU hWV
  rw [Scheme.Modules.map_smul]
  obtain ⟨v, rfl⟩ := hu
  let uW : (Γ(X, W))ˣ := Units.map (X.presheaf.map (homOfLE hWU).op).hom.toMonoidHom v
  have : (fun g : Γ(X, W) => g • ((X.presheaf.map (homOfLE hWU).op (v : Γ(X, U))) •
      M.presheaf.map (homOfLE hWU).op e)) =
      (fun g : Γ(X, W) => g • M.presheaf.map (homOfLE hWU).op e) ∘ (fun g => g * (uW : Γ(X, W))) := by
    funext g
    simp only [Function.comp_apply, smul_smul]
    rfl
  rw [this]
  exact hb.comp (uW.mulRight_bijective)

lemma exists_chart {M M' : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (hM' : Scheme.Modules.IsInvertible M') (x : X) :
    ∃ (V : X.affineOpens) (e : Γ(M, V.1)) (e' : Γ(M', V.1)),
      x ∈ V.1 ∧ Scheme.Modules.IsFrameOn e V.1 ∧ Scheme.Modules.IsFrameOn e' V.1 := by
  obtain ⟨U, f, hxU, hf⟩ := hM.exists_isFrameOn_monoidalV2 x
  obtain ⟨U', f', hxU', hf'⟩ := hM'.exists_isFrameOn_monoidalV2 x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ U ⊓ U' from ⟨hxU, hxU'⟩)
      (U ⊓ U').isOpen
  have h1 : V ≤ U := fun y hy => (hVle hy).1
  have h2 : V ≤ U' := fun y hy => (hVle hy).2
  exact ⟨⟨V, hV⟩, M.presheaf.map (homOfLE h1).op f, M'.presheaf.map (homOfLE h2).op f', hxV,
    (hf.map (homOfLE h1)).mono h1, (hf'.map (homOfLE h2)).mono h2⟩

lemma exists_coord {M : X.Modules} {V : X.Opens} {e : Γ(M, V)} (he : Scheme.Modules.IsFrameOn e V)
    (s : 𝟙_ X.Modules ⟶ M) :
    ∃ a : Γ(X, V), s.app V (Scheme.Modules.toUnitSection V 1) = a • e := by
  obtain ⟨a, ha⟩ := (he le_rfl le_rfl).2 (s.app V (Scheme.Modules.toUnitSection V 1))
  refine ⟨a, ?_⟩
  rw [← ha, mod_map_id]

noncomputable def frameEquiv {M : X.Modules} {V : X.Opens} (e : Γ(M, V))
    (he : Scheme.Modules.IsFrameOn e V) {W : X.Opens} (hW : W ≤ V) :
    Γ(X, W) ≃ₗ[Γ(X, W)] Γ(M, W) :=
  LinearEquiv.ofBijective
    ((LinearMap.id : Γ(X, W) →ₗ[Γ(X, W)] Γ(X, W)).smulRight (M.presheaf.map (homOfLE hW).op e)) (by
    have h : ⇑((LinearMap.id : Γ(X, W) →ₗ[Γ(X, W)] Γ(X, W)).smulRight
          (M.presheaf.map (homOfLE hW).op e))
        = fun g : Γ(X, W) => g • M.presheaf.map (homOfLE hW).op e := by
      funext g; simp [LinearMap.smulRight_apply]
    rw [h]; exact he hW hW)

lemma frameEquiv_apply {M : X.Modules} {V : X.Opens} (e : Γ(M, V))
    (he : Scheme.Modules.IsFrameOn e V) {W : X.Opens} (hW : W ≤ V) (g : Γ(X, W)) :
    frameEquiv e he hW g = g • M.presheaf.map (homOfLE hW).op e := by
  simp [frameEquiv, LinearMap.smulRight_apply]

lemma frameEquiv_symm_smul {M : X.Modules} {V : X.Opens} (e : Γ(M, V))
    (he : Scheme.Modules.IsFrameOn e V) {W : X.Opens} (hW : W ≤ V) (g : Γ(X, W)) :
    (frameEquiv e he hW).symm (g • M.presheaf.map (homOfLE hW).op e) = g := by
  rw [LinearEquiv.symm_apply_eq, frameEquiv_apply]

noncomputable def localMap {M M' : X.Modules} {V : X.Opens} (e : Γ(M, V))
    (he : Scheme.Modules.IsFrameOn e V) (e' : Γ(M', V)) (u : Γ(X, V)) {W : X.Opens} (hW : W ≤ V) :
    Γ(M, W) →ₗ[Γ(X, W)] Γ(M', W) :=
  ((LinearMap.id : Γ(X, W) →ₗ[Γ(X, W)] Γ(X, W)).smulRight
      (X.presheaf.map (homOfLE hW).op u • M'.presheaf.map (homOfLE hW).op e')).comp
    (frameEquiv e he hW).symm.toLinearMap

lemma localMap_smul {M M' : X.Modules} {V : X.Opens} (e : Γ(M, V))
    (he : Scheme.Modules.IsFrameOn e V) (e' : Γ(M', V)) (u : Γ(X, V)) {W : X.Opens} (hW : W ≤ V)
    (g : Γ(X, W)) :
    localMap e he e' u hW (g • M.presheaf.map (homOfLE hW).op e) =
      (g * X.presheaf.map (homOfLE hW).op u) • M'.presheaf.map (homOfLE hW).op e' := by
  simp only [localMap, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, frameEquiv_symm_smul,
    LinearMap.smulRight_apply, LinearMap.id_apply, smul_smul]

lemma app_one_eq_smul {M : X.Modules} (s : 𝟙_ X.Modules ⟶ M) {V W : X.Opens} (hW : W ≤ V)
    {e : Γ(M, V)} {a : Γ(X, V)} (hs : s.app V (Scheme.Modules.toUnitSection V 1) = a • e) :
    s.app W (Scheme.Modules.toUnitSection W 1) =
      X.presheaf.map (homOfLE hW).op a • M.presheaf.map (homOfLE hW).op e := by
  rw [app_one_eq_map s (homOfLE hW), hs, Scheme.Modules.map_smul]

lemma localMap_app_one {M M' : X.Modules} (s : 𝟙_ X.Modules ⟶ M) (s' : 𝟙_ X.Modules ⟶ M')
    {V : X.Opens} (e : Γ(M, V)) (he : Scheme.Modules.IsFrameOn e V) (e' : Γ(M', V))
    (u a : Γ(X, V))
    (hs : s.app V (Scheme.Modules.toUnitSection V 1) = a • e)
    (hs' : s'.app V (Scheme.Modules.toUnitSection V 1) = (u * a) • e')
    {W : X.Opens} (hW : W ≤ V) :
    localMap e he e' u hW (s.app W (Scheme.Modules.toUnitSection W 1)) =
      s'.app W (Scheme.Modules.toUnitSection W 1) := by
  rw [app_one_eq_smul s hW hs, localMap_smul, app_one_eq_smul s' hW hs', map_mul, mul_comm]

lemma localMap_eq [IsIntegral X] {M M' : X.Modules} (s : 𝟙_ X.Modules ⟶ M) (s' : 𝟙_ X.Modules ⟶ M')
    {V₁ : X.Opens} (e₁ : Γ(M, V₁)) (he₁ : Scheme.Modules.IsFrameOn e₁ V₁) (e₁' : Γ(M', V₁))
    (he₁' : Scheme.Modules.IsFrameOn e₁' V₁) (u₁ a₁ : Γ(X, V₁))
    (hs₁ : s.app V₁ (Scheme.Modules.toUnitSection V₁ 1) = a₁ • e₁)
    (hs₁' : s'.app V₁ (Scheme.Modules.toUnitSection V₁ 1) = (u₁ * a₁) • e₁') (ha₁ : a₁ ≠ 0)
    {V₂ : X.Opens} (e₂ : Γ(M, V₂)) (he₂ : Scheme.Modules.IsFrameOn e₂ V₂) (e₂' : Γ(M', V₂))
    (u₂ a₂ : Γ(X, V₂))
    (hs₂ : s.app V₂ (Scheme.Modules.toUnitSection V₂ 1) = a₂ • e₂)
    (hs₂' : s'.app V₂ (Scheme.Modules.toUnitSection V₂ 1) = (u₂ * a₂) • e₂')
    {W : X.Opens} (h₁ : W ≤ V₁) (h₂ : W ≤ V₂) :
    localMap e₁ he₁ e₁' u₁ h₁ = localMap e₂ he₂ e₂' u₂ h₂ := by

  have k₁ := localMap_app_one s s' e₁ he₁ e₁' u₁ a₁ hs₁ hs₁' h₁
  have k₂ := localMap_app_one s s' e₂ he₂ e₂' u₂ a₂ hs₂ hs₂' h₂
  set sW := s.app W (Scheme.Modules.toUnitSection W 1) with hsW
  set aW := X.presheaf.map (homOfLE h₁).op a₁ with haW
  set eW := M.presheaf.map (homOfLE h₁).op e₁ with heW
  set eW' := M'.presheaf.map (homOfLE h₁).op e₁' with heW'
  have hsW' : sW = aW • eW := app_one_eq_smul s h₁ hs₁
  apply LinearMap.ext
  intro m
  obtain ⟨g, rfl⟩ := (he₁ h₁ h₁).2 m

  have hm : aW • (g • eW) = g • sW := by rw [hsW', smul_smul, smul_smul, mul_comm]
  have key : ∀ (L : Γ(M, W) →ₗ[Γ(X, W)] Γ(M', W)),
      L sW = s'.app W (Scheme.Modules.toUnitSection W 1) →
      aW • L (g • eW) = g • s'.app W (Scheme.Modules.toUnitSection W 1) := by
    intro L hL
    rw [← L.map_smul, hm, L.map_smul, hL]
  have hdiff : aW • (localMap e₁ he₁ e₁' u₁ h₁ (g • eW) - localMap e₂ he₂ e₂' u₂ h₂ (g • eW)) = 0 := by
    rw [smul_sub, key _ k₁, key _ k₂, sub_self]
  obtain ⟨d, hd⟩ := (he₁' h₁ h₁).2
    (localMap e₁ he₁ e₁' u₁ h₁ (g • eW) - localMap e₂ he₂ e₂' u₂ h₂ (g • eW))
  change d • eW' = _ at hd
  rw [← hd, smul_smul, he₁'.smul_eq_zero_iff h₁ h₁] at hdiff

  have hd0 : d = 0 := by
    rcases (W : Set X).eq_empty_or_nonempty with hW | hW
    · obtain rfl : W = ⊥ := SetLike.ext' hW
      exact Subsingleton.elim _ _
    · haveI : Nonempty W := hW.to_subtype
      have haW0 : aW ≠ 0 := fun h0 =>
        ha₁ (map_injective_of_isIntegral X (homOfLE h₁) (by rw [map_zero]; exact h0))
      exact (mul_eq_zero.mp hdiff).resolve_left haW0
  rw [hd0, zero_smul] at hd
  exact (sub_eq_zero.mp hd.symm)

end B1Aux

open B1Aux in
theorem solution
    {X : Scheme.{u}} [IsIntegral X] {M M' : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (hM' : Scheme.Modules.IsInvertible M')
    (s : 𝟙_ X.Modules ⟶ M) (s' : 𝟙_ X.Modules ⟶ M') (hs : s ≠ 0)
    (h : Scheme.Modules.zeroSchemeIdeal s = Scheme.Modules.zeroSchemeIdeal s') :
    Nonempty (M ≅ M') := by
  classical

  choose V e e' hxV he he' using fun x : X => exists_chart hM hM' x
  choose a ha using fun x : X => exists_coord (he x) s
  choose a' ha' using fun x : X => exists_coord (he' x) s'
  have hne : ∀ x : X, Nonempty ((V x).1) := fun x => ⟨⟨x, hxV x⟩⟩

  have hZ : ∀ x : X, (Scheme.Modules.zeroSchemeIdeal s).ideal (V x) = Ideal.span {a x} := by
    intro x
    have := hM.ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul_monoidalV2 (e x) (he x) s (a x) (ha x)
      (V x) le_rfl
    rwa [ring_map_id] at this
  have hZ' : ∀ x : X, (Scheme.Modules.zeroSchemeIdeal s').ideal (V x) = Ideal.span {a' x} := by
    intro x
    have := hM'.ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul_monoidalV2 (e' x) (he' x) s' (a' x)
      (ha' x) (V x) le_rfl
    rwa [ring_map_id] at this

  have ha0 : ∀ x : X, a x ≠ 0 := by
    intro x hax
    apply hM.genericPoint_notMem_support_zeroSchemeIdeal_monoidalV2 s hs
    have hη : genericPoint X ∈ (V x).1 :=
      ((genericPoint_spec X).mem_open_set_iff (V x).1.isOpen).mpr ⟨x, trivial, hxV x⟩
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := V x) hη, hZ x, hax,
      Scheme.mem_zeroLocus_iff]
    intro f hf
    have hf0 : f = 0 := by simpa using hf
    rw [hf0, Scheme.basicOpen_zero]
    exact fun hbot => hbot

  have hu : ∀ x : X, ∃ u : Γ(X, (V x).1), IsUnit u ∧ a' x = u * a x := by
    intro x
    haveI := hne x
    have hsp : Ideal.span {a x} = Ideal.span {a' x} := by rw [← hZ x, ← hZ' x, h]
    obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hsp
    exact ⟨v, v.isUnit, by rw [← hv, mul_comm]⟩
  choose u hu hau using hu
  have ha'' : ∀ x : X, s'.app (V x).1 (Scheme.Modules.toUnitSection (V x).1 1) = (u x * a x) • e' x :=
    fun x => by rw [ha' x, hau x]

  have hcov : (⨆ x : X, (V x).1) = ⊤ :=
    eq_top_iff.mpr fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hxV y⟩

  let f : ∀ W : X.Opens, (∃ x : X, W ≤ (V x).1) → (Γ(M, W) →ₗ[Γ(X, W)] Γ(M', W)) :=
    fun W hW => localMap (e hW.choose) (he hW.choose) (e' hW.choose) (u hW.choose) hW.choose_spec
  have hf : ∀ (W : X.Opens) (hW : ∃ x : X, W ≤ (V x).1) (y : X) (hy : W ≤ (V y).1),
      f W hW = localMap (e y) (he y) (e' y) (u y) hy := fun W hW y hy =>
    localMap_eq s s' (e hW.choose) (he hW.choose) (e' hW.choose) (he' hW.choose) (u hW.choose)
      (a hW.choose) (ha hW.choose) (ha'' hW.choose) (ha0 hW.choose)
      (e y) (he y) (e' y) (u y) (a y) (ha y) (ha'' y) hW.choose_spec hy

  obtain ⟨F, hF, -⟩ := Scheme.Modules.existsUnique_hom_app_eq_of_iSup_eq_top M M'
    (fun x : X => (V x).1) hcov f (by
      intro W W' hW hle m
      obtain ⟨x, hx⟩ := hW
      have hW : (∃ x : X, W ≤ (V x).1) := ⟨x, hx⟩
      show M'.presheaf.map (homOfLE hle).op (f W hW m) = f W' _ (M.presheaf.map (homOfLE hle).op m)
      rw [hf W hW x hx, hf W' _ x (hle.trans hx)]
      obtain ⟨g, rfl⟩ := ((he x) hx hx).2 m
      change M'.presheaf.map (homOfLE hle).op
          (localMap (e x) (he x) (e' x) (u x) hx (g • M.presheaf.map (homOfLE hx).op (e x))) = _
      rw [localMap_smul, Scheme.Modules.map_smul, Scheme.Modules.map_smul, map_mul, mod_map_map,
        mod_map_map, ring_map_map, localMap_smul])

  have hFe : ∀ x : X, F.app (V x).1 (e x) = u x • e' x := by
    intro x
    rw [hF (V x).1 ⟨x, le_rfl⟩ (e x), hf (V x).1 ⟨x, le_rfl⟩ x le_rfl]
    have key := localMap_smul (e x) (he x) (e' x) (u x) (le_refl _) (1 : Γ(X, (V x).1))
    simp only [one_smul, one_mul, mod_map_id, ring_map_id] at key
    exact key
  haveI : IsIso F := Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top_monoidalV2 F
    (fun x : X => (V x).1) hcov (fun x => e x) (fun x => u x • e' x) (fun x => he x)
    (fun x => isFrameOn_smul (he' x) (hu x)) hFe
  exact ⟨asIso F⟩

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_zeroSchemeIdeal_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_zeroSchemeIdeal_eq (solution)
