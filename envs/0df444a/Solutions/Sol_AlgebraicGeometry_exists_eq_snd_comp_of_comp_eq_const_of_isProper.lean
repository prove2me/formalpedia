-- Prove2me | solution 1 for AlgebraicGeometry.exists_eq_snd_comp_of_comp_eq_const_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/5e041581-2657-54de-8c69-068f1c26524c

import Mathlib
import Theorems.Thm_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_eq_snd_comp_of_comp_eq_const_of_isProper

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_eq_snd_comp_of_comp_eq_const_of_isProper.AlgebraicGeometry TopologicalSpace Polynomial AlgebraicGeometry.Polynomial"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.resLE_comp_ι Scheme.Hom.congr_app Scheme.Hom.map_appLE Surjective HasAffineProperty IsProper basicOpen_eq_bot_iff Scheme.Hom.id_app Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Γ IsIntegralHom.SpecMap_iff Scheme.isoSpec_hom ext_of_isAffine IsIntegralHom UniversallyClosed QuasiCompact Scheme.Pullback.range_fst IsAffine isPullback_morphismRestrict Scheme.preimage_basicOpen Spec IsIntegral Scheme.Hom.id_appTop Spec.map Scheme.toSpecΓ_naturality Scheme Scheme.Hom.appTop QuasiCompact.compactSpace_of_compactSpace Scheme.Hom.comp_appLE Scheme.basicOpen_zero Scheme.Hom.comp_base HasAffineProperty.iff_of_isAffine Scheme.Hom.comp_appTop IsClosedImmersion IsSeparated IsIntegralHom.iff_universallyClosed_and_isAffineHom Scheme.Hom.comp_app SpecMap_ΓSpecIso_hom Spec.map_id IsProper.of_comp UniversallyClosed.of_comp_surjective IsAffineOpen Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.toSpecΓ_preimage_basicOpen Scheme.Cover.hom_ext Scheme.Hom.resLE_eq_morphismRestrict Scheme.Hom.resLE_app_top toSpecΓ quasiSeparated_iff_quasiSeparatedSpace range_eq_univ IsIntegral.component_integral Scheme.Cover Scheme.ΓSpecIso bijective_appTop_pullback_snd_of_bijective_appTop" end AlgebraicGeometry
p2m_open_scoped "AlgebraicGeometry" in

theorem AlgebraicGeometry.bijective_algebraMap_appTop_of_isProper_of_isIntegral_of_section
    (k : Type u) [Field k] {X : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) [IsProper fX] [IsIntegral X]
    (x₀ : Spec (CommRingCat.of k) ⟶ X) (hx₀ : x₀ ≫ fX = 𝟙 _) :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom := by
  set φ : k →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom with hφ
  haveI : Nonempty (⊤ : X.Opens) := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    exact ⟨⟨x, trivial⟩⟩
  haveI : IsDomain Γ(X, ⊤) := IsIntegral.component_integral ⊤

  let ev : Γ(X, ⊤) →+* k := (x₀.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom
  have hev : ∀ c : k, ev (φ c) = c := by
    intro c
    change (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop) ≫
      (x₀.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom)).hom c = c
    rw [Category.assoc, ← Category.assoc fX.appTop, ← Scheme.Hom.comp_appTop, hx₀, Scheme.Hom.id_appTop,
      Category.id_comp, Iso.inv_hom_id]
    rfl
  refine ⟨φ.injective, fun a => ?_⟩

  suffices key : ∀ a' : Γ(X, ⊤), ev a' = 0 → a' = 0 by
    refine ⟨ev a, ?_⟩
    have h := key (a - φ (ev a)) (by rw [map_sub, hev, sub_self])
    exact (sub_eq_zero.mp h).symm
  intro a' ha'

  let ψ : k[X] →+* Γ(X, ⊤) := Polynomial.eval₂RingHom φ a'
  let g : X ⟶ Spec (CommRingCat.of k[X]) := X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)
  let π : Spec (CommRingCat.of k[X]) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k k[X]))
  have hψC : ψ.comp (algebraMap k k[X]) = φ := by
    ext x
    simp [ψ, Polynomial.algebraMap_eq]
  have hfX : fX = X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) := by
    have h1 := Scheme.toSpecΓ_naturality fX
    rw [← SpecMap_ΓSpecIso_hom] at h1
    calc fX = (fX ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom) ≫
          Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv := by
            rw [Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
      _ = X.toSpecΓ ≫ Spec.map fX.appTop ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv := by
            rw [h1, Category.assoc]
      _ = X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) := by
            rw [← Spec.map_comp, hφ, CommRingCat.ofHom_hom]
  have hgπ : g ≫ π = fX := by
    rw [hfX]
    change (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k k[X])) = _
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψC]
  haveI : IsProper (g ≫ π) := by rw [hgπ]; infer_instance
  haveI : IsProper g := IsProper.of_comp g π

  have hgx : ∀ x : X, (g.base x).asIdeal = Ideal.comap ψ (X.toSpecΓ.base x).asIdeal := fun x => rfl
  have hT : ∀ x : X, Polynomial.X ∈ (g.base x).asIdeal ↔ x ∉ X.basicOpen a' := by
    intro x
    rw [hgx, Ideal.mem_comap, show ψ Polynomial.X = a' by simp [ψ]]
    constructor
    · intro h hx
      have h5 : x ∈ X.toSpecΓ ⁻¹ᵁ (PrimeSpectrum.basicOpen a') := by
        rw [Scheme.toSpecΓ_preimage_basicOpen]; exact hx
      exact (PrimeSpectrum.mem_basicOpen _ _).mp h5 h
    · intro hx
      by_contra h
      apply hx
      have h5 : x ∈ X.toSpecΓ ⁻¹ᵁ (PrimeSpectrum.basicOpen a') := (PrimeSpectrum.mem_basicOpen _ _).mpr h
      rwa [Scheme.toSpecΓ_preimage_basicOpen] at h5

  let pt : ↥(Spec (CommRingCat.of k)) := IsLocalRing.closedPoint k
  have hx₀a : x₀.appTop a' = 0 := by
    have h1 : (Scheme.ΓSpecIso (CommRingCat.of k)).hom (x₀.appTop a') = 0 := ha'
    have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).hom).1
    exact hinj (h1.trans (map_zero _).symm)
  have hpt : x₀.base pt ∉ X.basicOpen a' := by
    intro h
    have h2 : pt ∈ x₀ ⁻¹ᵁ (X.basicOpen a') := h
    rw [Scheme.preimage_basicOpen] at h2
    change pt ∈ (Spec (CommRingCat.of k)).basicOpen (x₀.appTop a') at h2
    rw [hx₀a, Scheme.basicOpen_zero] at h2
    exact h2

  have hnsurj : ¬ Function.Surjective g.base := by
    intro hsurj
    haveI : Surjective g := ⟨hsurj⟩
    have hπ : UniversallyClosed π := UniversallyClosed.of_comp_surjective g π
    have hint : IsIntegralHom π :=
      IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨hπ, inferInstance⟩
    have hI : (algebraMap k k[X]).IsIntegral := IsIntegralHom.SpecMap_iff.mp hint
    haveI : Algebra.IsIntegral k k[X] := ⟨hI⟩
    exact Polynomial.not_finite (Algebra.IsIntegral.finite (R := k) (A := k[X]))

  have hclosed : IsClosed (Set.range g.base) := g.isClosedMap.isClosed_range
  have hirr : IsIrreducible (Set.range g.base) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ X).image _ g.base.hom.continuous.continuousOn
  set 𝔭 := PrimeSpectrum.vanishingIdeal (Set.range g.base) with h𝔭def
  have h𝔭 : 𝔭.IsPrime := PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp hirr
  have hrange : Set.range g.base = PrimeSpectrum.zeroLocus (𝔭 : Set k[X]) := by
    rw [h𝔭def, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact hclosed.closure_eq.symm
  have hne : 𝔭 ≠ ⊥ := by
    intro h
    apply hnsurj
    intro P
    have : P ∈ Set.range g.base := by
      rw [hrange, h, PrimeSpectrum.zeroLocus_bot]
      exact Set.mem_univ _
    exact this
  have hmax : 𝔭.IsMaximal := h𝔭.isMaximal hne
  have hall : ∀ x : X, (g.base x).asIdeal = 𝔭 := by
    intro x
    have hmem : g.base x ∈ PrimeSpectrum.zeroLocus (𝔭 : Set k[X]) := hrange ▸ ⟨x, rfl⟩
    exact (hmax.eq_of_le (g.base x).2.ne_top hmem).symm

  have hTp : Polynomial.X ∈ 𝔭 := by
    rw [← hall (x₀.base pt)]
    exact (hT _).mpr hpt

  have hval : ∀ x : X, x ∉ X.basicOpen a' := fun x => (hT x).mp ((hall x).symm ▸ hTp)
  have hbot : X.basicOpen a' = ⊥ := le_bot_iff.mp fun x hx => (hval x hx).elim
  exact (basicOpen_eq_bot_iff _).mp hbot

p2m_open_scoped "AlgebraicGeometry" in

theorem AlgebraicGeometry.exists_opens_ι_comp_eq_of_isClosedMap_of_app_bijective_of_isAffineOpen
    {S X Y : Scheme.{u}} (p : X ⟶ S) (hp : IsClosedMap p.base)
    (hO : ∀ U : S.Opens, IsAffineOpen U → Function.Bijective (p.app U).hom)
    (ε : S ⟶ X) (hε : ε ≫ p = 𝟙 S)
    (f : X ⟶ Y) (s : S) (y₀ : Y) (hs : ∀ x : X, p.base x = s → f.base x = y₀) :
    ∃ U : S.Opens, s ∈ U ∧ (p ⁻¹ᵁ U).ι ≫ f = (p ⁻¹ᵁ U).ι ≫ p ≫ ε ≫ f := by

  obtain ⟨V, hV, hy₀V⟩ : ∃ V : Y.Opens, IsAffineOpen V ∧ y₀ ∈ V := by
    obtain ⟨V, hV, hmem, -⟩ := (Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) (show y₀ ∈ (⊤ : Y.Opens) from trivial)
    exact ⟨V, hV, hmem⟩

  have hclosed : IsClosed (p.base '' ((f ⁻¹ᵁ V : Set X)ᶜ)) := hp _ (f ⁻¹ᵁ V).2.isClosed_compl
  let U0 : S.Opens := ⟨(p.base '' ((f ⁻¹ᵁ V : Set X)ᶜ))ᶜ, hclosed.isOpen_compl⟩
  have hsU0 : s ∈ U0 := by
    rintro ⟨x, hx, hxs⟩
    exact hx (show f.base x ∈ V from (hs x hxs).symm ▸ hy₀V)

  obtain ⟨U, hUaff, hsU, hUU0⟩ : ∃ U : S.Opens, IsAffineOpen U ∧ s ∈ U ∧ U ≤ U0 := by
    obtain ⟨U, hU, hmem, hle⟩ := (Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens) hsU0
    exact ⟨U, hU, hmem, hle⟩
  have hε_base : ∀ u : S, p.base (ε.base u) = u := fun u => by
    change (ε ≫ p).base u = u
    rw [hε]; rfl
  set W : X.Opens := p ⁻¹ᵁ U with hW
  have e₁ : W ≤ f ⁻¹ᵁ V := by
    intro x hx
    by_contra hxV
    exact hUU0 hx ⟨x, hxV, rfl⟩
  have hle : U ≤ (ε ≫ f) ⁻¹ᵁ V := by
    intro u hu
    have : ε.base u ∈ W := by
      change p.base (ε.base u) ∈ U
      rw [hε_base]; exact hu
    exact e₁ this
  have e₂ : W ≤ (p ≫ ε ≫ f) ⁻¹ᵁ V := fun x hx => hle hx
  refine ⟨U, hsU, ?_⟩

  haveI : IsAffine V := hV
  suffices key : f.appLE V W e₁ = (p ≫ ε ≫ f).appLE V W e₂ by
    have h1 : f.resLE V W e₁ = (p ≫ ε ≫ f).resLE V W e₂ := by
      apply ext_of_isAffine
      change (f.resLE V W e₁).app ⊤ = ((p ≫ ε ≫ f).resLE V W e₂).app ⊤
      rw [Scheme.Hom.resLE_app_top, Scheme.Hom.resLE_app_top, key]
    have h2 := congrArg (· ≫ V.ι) h1
    simp only [Scheme.Hom.resLE_comp_ι] at h2
    exact h2

  let r : Γ(S, U) ⟶ Γ(X, W) := p.app U
  have hr : Function.Bijective r.hom := hO U hUaff
  let t : Γ(X, W) ⟶ Γ(S, ε ⁻¹ᵁ W) := ε.app W
  have heqW : ε ⁻¹ᵁ W = U := by
    change (ε ≫ p) ⁻¹ᵁ U = U
    rw [hε]; rfl
  have hrt : r ≫ t = S.presheaf.map (eqToHom heqW).op := by
    change p.app U ≫ ε.app (p ⁻¹ᵁ U) = _
    rw [← Scheme.Hom.comp_app, Scheme.Hom.congr_app hε U, Scheme.Hom.id_app]
    exact Category.id_comp _

  ext φ₀
  obtain ⟨b, hb⟩ := hr.2 (f.appLE V W e₁ φ₀)

  have hB : (p ≫ ε ≫ f).appLE V W e₂ =
      (ε ≫ f).app V ≫ S.presheaf.map (homOfLE hle).op ≫ r := by
    rw [Scheme.Hom.comp_appLE]
    congr 1
    rw [show r = p.appLE U W le_rfl from Scheme.Hom.app_eq_appLE p, Scheme.Hom.map_appLE]

  have hA : f.appLE V W e₁ ≫ t = (ε ≫ f).appLE V (ε ⁻¹ᵁ W) (by rw [heqW]; exact hle) := by
    change f.appLE V W e₁ ≫ ε.app W = _
    rw [Scheme.Hom.app_eq_appLE ε, Scheme.Hom.appLE_comp_appLE]
  have hC : ((ε ≫ f).app V ≫ S.presheaf.map (homOfLE hle).op) ≫ S.presheaf.map (eqToHom heqW).op =
      (ε ≫ f).appLE V (ε ⁻¹ᵁ W) (by rw [heqW]; exact hle) := by
    rw [Scheme.Hom.app_eq_appLE, Category.assoc, ← Functor.map_comp, Scheme.Hom.appLE_map]

  have hb' : (S.presheaf.map (eqToHom heqW).op) b =
      (S.presheaf.map (eqToHom heqW).op) (((ε ≫ f).app V ≫ S.presheaf.map (homOfLE hle).op) φ₀) := by
    have h1 : (S.presheaf.map (eqToHom heqW).op) b = (r ≫ t) b := by rw [hrt]
    rw [h1, CommRingCat.comp_apply, hb, ← CommRingCat.comp_apply, hA, ← CommRingCat.comp_apply, hC]
  have hinj : Function.Injective (S.presheaf.map (eqToHom heqW).op).hom :=
    (ConcreteCategory.bijective_of_isIso (S.presheaf.map (eqToHom heqW).op)).1
  have hbb := hinj hb'
  rw [← hb, hB, hbb]
  rfl

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.resLE_comp_ι Scheme.Hom.congr_app Scheme.Hom.map_appLE Surjective HasAffineProperty IsProper basicOpen_eq_bot_iff Scheme.Hom.id_app Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Γ IsIntegralHom.SpecMap_iff Scheme.isoSpec_hom ext_of_isAffine IsIntegralHom UniversallyClosed QuasiCompact Scheme.Pullback.range_fst IsAffine isPullback_morphismRestrict Scheme.preimage_basicOpen Spec IsIntegral Scheme.Hom.id_appTop Spec.map Scheme.toSpecΓ_naturality Scheme Scheme.Hom.appTop QuasiCompact.compactSpace_of_compactSpace Scheme.Hom.comp_appLE Scheme.basicOpen_zero Scheme.Hom.comp_base HasAffineProperty.iff_of_isAffine Scheme.Hom.comp_appTop IsClosedImmersion IsSeparated IsIntegralHom.iff_universallyClosed_and_isAffineHom Scheme.Hom.comp_app SpecMap_ΓSpecIso_hom Spec.map_id IsProper.of_comp UniversallyClosed.of_comp_surjective IsAffineOpen Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.toSpecΓ_preimage_basicOpen Scheme.Cover.hom_ext Scheme.Hom.resLE_eq_morphismRestrict Scheme.Hom.resLE_app_top toSpecΓ quasiSeparated_iff_quasiSeparatedSpace range_eq_univ IsIntegral.component_integral Scheme.Cover Scheme.ΓSpecIso bijective_appTop_pullback_snd_of_bijective_appTop" namespace RigidityAux end AlgebraicGeometry.RigidityAux
p2m_open_scoped "AlgebraicGeometry" in

theorem AlgebraicGeometry.RigidityAux.bijective_iso_comp_iso_iff {A B C D : CommRingCat.{u}}
    (e : A ⟶ B) (he : Function.Bijective e.hom) (f : B ⟶ C) (e' : C ⟶ D) (he' : Function.Bijective e'.hom) :
    Function.Bijective (e ≫ f ≫ e').hom ↔ Function.Bijective f.hom := by
  change Function.Bijective (e'.hom ∘ f.hom ∘ e.hom) ↔ _
  rw [← Function.comp_assoc, Function.Bijective.of_comp_iff _ he, Function.Bijective.of_comp_iff' he']

p2m_open_scoped "AlgebraicGeometry" in
theorem AlgebraicGeometry.RigidityAux.bijective_app_pullback_snd_of_isAffineOpen
    {k : Type u} [Field k] {X Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [QuasiSeparatedSpace X]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom)
    (fY : Y ⟶ Spec (CommRingCat.of k)) (V : Y.Opens) (hV : IsAffineOpen V) :
    Function.Bijective ((pullback.snd fX fY).app V).hom := by
  haveI : IsAffine V := hV

  let q := (pullback.snd fX fY).resLE V ((pullback.snd fX fY) ⁻¹ᵁ V) le_rfl
  have hq : q.appTop = V.topIso.hom ≫ (pullback.snd fX fY).app V ≫ ((pullback.snd fX fY) ⁻¹ᵁ V).topIso.inv := by
    change q.app ⊤ = _
    rw [Scheme.Hom.resLE_app_top, ← Scheme.Hom.app_eq_appLE]

  rw [← AlgebraicGeometry.RigidityAux.bijective_iso_comp_iso_iff V.topIso.hom (ConcreteCategory.bijective_of_isIso _)
    _ ((pullback.snd fX fY) ⁻¹ᵁ V).topIso.inv (ConcreteCategory.bijective_of_isIso _), ← hq]

  let gV : (V : Scheme.{u}) ⟶ Spec (CommRingCat.of k) := V.ι ≫ fY
  have H1 : IsPullback q (((pullback.snd fX fY) ⁻¹ᵁ V).ι ≫ pullback.fst fX fY) gV fX := by
    have h := (isPullback_morphismRestrict (pullback.snd fX fY) V)

    rw [← Scheme.Hom.resLE_eq_morphismRestrict] at h
    exact h.paste_vert (IsPullback.of_hasPullback fX fY).flip

  let B : CommRingCat.{u} := Γ(V, ⊤)
  let r : k →+* B := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ gV.appTop).hom
  letI : Algebra k B := r.toAlgebra
  have hgV : gV = (V : Scheme.{u}).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
    rw [Scheme.isoSpec_hom, RingHom.algebraMap_toAlgebra]
    have h1 := Scheme.toSpecΓ_naturality gV
    rw [← SpecMap_ΓSpecIso_hom] at h1
    calc gV = (gV ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom) ≫
          Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv := by
            rw [Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
      _ = (V : Scheme.{u}).toSpecΓ ≫ Spec.map gV.appTop ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv := by
            rw [h1, Category.assoc]
      _ = (V : Scheme.{u}).toSpecΓ ≫ Spec.map (CommRingCat.ofHom r) := by
            rw [← Spec.map_comp]; rfl

  have H2 : IsPullback (((pullback.snd fX fY) ⁻¹ᵁ V).ι ≫ pullback.fst fX fY)
      (q ≫ (V : Scheme.{u}).isoSpec.hom) fX (Spec.map (CommRingCat.ofHom (algebraMap k B))) := by
    refine H1.flip.of_iso (Iso.refl _) (Iso.refl _) (V : Scheme.{u}).isoSpec (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · rw [Iso.refl_hom, Category.comp_id, ← hgV]

  have hC := AlgebraicGeometry.bijective_appTop_pullback_snd_of_bijective_appTop fX hX B
  have e2 : H2.isoPullback.hom ≫ pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k B))) =
      q ≫ (V : Scheme.{u}).isoSpec.hom := H2.isoPullback_hom_snd
  have hj : Function.Bijective (Scheme.Hom.appTop H2.isoPullback.hom).hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.Γ.map H2.isoPullback.hom.op)
  have hiso : Function.Bijective ((Scheme.ΓSpecIso B).inv ≫ Scheme.Hom.appTop (V : Scheme.{u}).isoSpec.hom).hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.Γ.map (V : Scheme.{u}).isoSpec.hom.op)).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).inv)
  have hC' : Function.Bijective ((Scheme.ΓSpecIso B).inv ≫ (q ≫ (V : Scheme.{u}).isoSpec.hom).appTop).hom := by
    have h := (AlgebraicGeometry.RigidityAux.bijective_iso_comp_iso_iff (𝟙 _) Function.bijective_id
      ((Scheme.ΓSpecIso B).inv ≫ (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k B)))).appTop)
      (Scheme.Hom.appTop H2.isoPullback.hom) hj).mpr hC
    rw [← e2, Scheme.Hom.comp_appTop]
    simp only [Category.id_comp, Category.assoc] at h
    exact h

  rw [Scheme.Hom.comp_appTop, ← Category.assoc] at hC'
  exact (AlgebraicGeometry.RigidityAux.bijective_iso_comp_iso_iff
    ((Scheme.ΓSpecIso B).inv ≫ Scheme.Hom.appTop (V : Scheme.{u}).isoSpec.hom) hiso q.appTop (𝟙 _)
    Function.bijective_id).mp
    (by simpa only [Category.comp_id, Category.assoc] using hC')

theorem solution
    (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) [IsProper fX] [IsIntegral X]
    (fY : Y ⟶ Spec (CommRingCat.of k)) (hY : ConnectedSpace Y)
    (fZ : Z ⟶ Spec (CommRingCat.of k)) [IsSeparated fZ]
    (x₀ : Spec (CommRingCat.of k) ⟶ X) (hx₀ : x₀ ≫ fX = 𝟙 _)
    (y₀ : Spec (CommRingCat.of k) ⟶ Y) (hy₀ : y₀ ≫ fY = 𝟙 _)
    (φ : pullback fX fY ⟶ Z) (hφ : φ ≫ fZ = pullback.fst fX fY ≫ fX)
    (z₀ : Spec (CommRingCat.of k) ⟶ Z)
    (hconst : pullback.lift (𝟙 X) (fX ≫ y₀) (by rw [Category.id_comp, Category.assoc, hy₀, Category.comp_id]) ≫ φ = fX ≫ z₀) :
    φ = pullback.snd fX fY ≫ (pullback.lift (fY ≫ x₀) (𝟙 Y) (by rw [Category.assoc, hx₀, Category.comp_id, Category.id_comp]) ≫ φ) := by
  have hεp : (pullback.lift (fY ≫ x₀) (𝟙 Y) (by rw [Category.assoc, hx₀, Category.comp_id, Category.id_comp])) ≫ (pullback.snd fX fY) = 𝟙 Y := pullback.lift_snd _ _ _

  have hpc : IsClosedMap (pullback.snd fX fY).base := (pullback.snd fX fY).isClosedMap
  have hpo : IsOpenMap (pullback.snd fX fY).base := (pullback.snd fX fY).isOpenMap

  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace fX
  haveI : QuasiSeparatedSpace X := (quasiSeparated_iff_quasiSeparatedSpace fX).mp inferInstance
  have hXΓ := AlgebraicGeometry.bijective_algebraMap_appTop_of_isProper_of_isIntegral_of_section k fX x₀ hx₀
  have hO : ∀ U : Y.Opens, IsAffineOpen U → Function.Bijective ((pullback.snd fX fY).app U).hom := fun U hU =>
    AlgebraicGeometry.RigidityAux.bijective_app_pullback_snd_of_isAffineOpen fX hXΓ fY U hU

  have hloc : ∀ (y : Y) (z : Z), (∀ w : ↥(pullback fX fY), (pullback.snd fX fY).base w = y → φ.base w = z) →
      ∃ U : Y.Opens, y ∈ U ∧ ((pullback.snd fX fY) ⁻¹ᵁ U).ι ≫ φ = ((pullback.snd fX fY) ⁻¹ᵁ U).ι ≫ (pullback.snd fX fY) ≫ (pullback.lift (fY ≫ x₀) (𝟙 Y) (by rw [Category.assoc, hx₀, Category.comp_id, Category.id_comp])) ≫ φ :=
    fun y z h => AlgebraicGeometry.exists_opens_ι_comp_eq_of_isClosedMap_of_app_bijective_of_isAffineOpen
      (pullback.snd fX fY) hpc hO (pullback.lift (fY ≫ x₀) (𝟙 Y) (by rw [Category.assoc, hx₀, Category.comp_id, Category.id_comp])) hεp φ y z h

  haveI : Z.IsSeparated := (HasAffineProperty.iff_of_isAffine (P := @IsSeparated)).mp (inferInstance : IsSeparated fZ)
  let ι := equalizer.ι φ ((pullback.snd fX fY) ≫ (pullback.lift (fY ≫ x₀) (𝟙 Y) (by rw [Category.assoc, hx₀, Category.comp_id, Category.id_comp])) ≫ φ)
  haveI : IsClosedImmersion ι := inferInstance
  have hEclosed : IsClosed (Set.range ι.base) := ι.isClosedEmbedding.isClosed_range

  let T : Set Y := {y | ∃ U : Y.Opens, y ∈ U ∧ ((pullback.snd fX fY) ⁻¹ᵁ U).ι ≫ φ = ((pullback.snd fX fY) ⁻¹ᵁ U).ι ≫ (pullback.snd fX fY) ≫ (pullback.lift (fY ≫ x₀) (𝟙 Y) (by rw [Category.assoc, hx₀, Category.comp_id, Category.id_comp])) ≫ φ}
  have hTopen : IsOpen T := by
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨U, hyU, hU⟩
    exact ⟨U, fun y' hy' => ⟨U, hy', hU⟩, U.2, hyU⟩
  have hT : T = ((pullback.snd fX fY).base '' (Set.range ι.base)ᶜ)ᶜ := by
    ext y
    constructor
    · rintro ⟨U, hyU, hU⟩ ⟨w, hw, hwy⟩
      apply hw
      have hwU : w ∈ (pullback.snd fX fY) ⁻¹ᵁ U := by change (pullback.snd fX fY).base w ∈ U; rw [hwy]; exact hyU
      refine ⟨(equalizer.lift ((pullback.snd fX fY) ⁻¹ᵁ U).ι hU).base ⟨w, hwU⟩, ?_⟩
      change ((equalizer.lift ((pullback.snd fX fY) ⁻¹ᵁ U).ι hU) ≫ ι).base ⟨w, hwU⟩ = w
      rw [equalizer.lift_ι]
      rfl
    · intro hy
      have hfib : ∀ w : ↥(pullback fX fY), (pullback.snd fX fY).base w = y → φ.base w = ((pullback.lift (fY ≫ x₀) (𝟙 Y) (by rw [Category.assoc, hx₀, Category.comp_id, Category.id_comp])) ≫ φ).base y := by
        intro w hwy
        have hwE : w ∈ Set.range ι.base := by
          by_contra hw
          exact hy ⟨w, hw, hwy⟩
        obtain ⟨e, rfl⟩ := hwE
        change (ι ≫ φ).base e = _
        rw [equalizer.condition]
        change ((pullback.lift (fY ≫ x₀) (𝟙 Y) (by rw [Category.assoc, hx₀, Category.comp_id, Category.id_comp])) ≫ φ).base ((pullback.snd fX fY).base (ι.base e)) = _
        rw [hwy]
      exact hloc y _ hfib
  have hTclosed : IsClosed T := by
    rw [hT]
    exact (hpo _ hEclosed.isOpen_compl).isClosed_compl

  have hy₀T : T.Nonempty := by
    let pt : ↥(Spec (CommRingCat.of k)) := IsLocalRing.closedPoint k
    refine ⟨y₀.base pt, hloc _ (z₀.base pt) fun w hw => ?_⟩
    let sl : X ⟶ pullback fX fY := pullback.lift (𝟙 X) (fX ≫ y₀)
      (by rw [Category.id_comp, Category.assoc, hy₀, Category.comp_id])
    have hw' : w ∈ Set.range sl.base := by

      have hsq : IsPullback sl fX (pullback.snd fX fY) y₀ := by
        refine IsPullback.of_right (h₁₂ := pullback.fst fX fY) (h₂₂ := fY) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback fX fY)
        have e1 : sl ≫ pullback.fst fX fY = 𝟙 X := pullback.lift_fst _ _ _
        rw [e1, hy₀]
        exact IsPullback.of_horiz_isIso ⟨by simp⟩
      have hr : Set.range sl.base = (pullback.snd fX fY).base ⁻¹' Set.range y₀.base := by
        rw [← Scheme.Pullback.range_fst (pullback.snd fX fY) y₀, ← hsq.isoPullback_hom_fst]
        change Set.range ((hsq.isoPullback.hom ≫ pullback.fst (pullback.snd fX fY) y₀).base) = _
        rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
          Set.range_eq_univ.mpr (ConcreteCategory.bijective_of_isIso hsq.isoPullback.hom.base).2, Set.image_univ]
      rw [hr]
      exact ⟨pt, hw.symm⟩
    obtain ⟨x, rfl⟩ := hw'
    change (sl ≫ φ).base x = _
    rw [hconst]
    change z₀.base (fX.base x) = z₀.base pt
    congr 1
    exact Subsingleton.elim _ _

  have hTuniv : T = Set.univ := by
    haveI := hY
    exact IsClopen.eq_univ ⟨hTclosed, hTopen⟩ hy₀T

  have hcov : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ ((pullback.snd fX fY) ⁻¹ᵁ U).ι ≫ φ = ((pullback.snd fX fY) ⁻¹ᵁ U).ι ≫ (pullback.snd fX fY) ≫ (pullback.lift (fY ≫ x₀) (𝟙 Y) (by rw [Category.assoc, hx₀, Category.comp_id, Category.id_comp])) ≫ φ :=
    fun y => (hTuniv ▸ Set.mem_univ y : y ∈ T)
  choose U hU using hcov
  let 𝒰 := (pullback fX fY).openCoverOfIsOpenCover (fun y : Y => (pullback.snd fX fY) ⁻¹ᵁ U y)
    (IsOpenCover.mk (eq_top_iff.mpr fun w _ => Opens.mem_iSup.mpr ⟨(pullback.snd fX fY).base w, (hU _).1⟩))
  exact Scheme.Cover.hom_ext 𝒰 _ _ fun y => (hU y).2

end S_AlgebraicGeometry_exists_eq_snd_comp_of_comp_eq_const_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_exists_eq_snd_comp_of_comp_eq_const_of_isProper (solution)
