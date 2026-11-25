-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.finrank_fibre_eq_of_isProper_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T01:57:08.892369+00:00
-- url     : https://prove2.me/submissions/e32b62ca-820d-4852-a185-acd9806aca60

import Mathlib

/-!
# S4-IntersectB, file Fam1: flat neighbourhoods of finite fibres (O8, part 1)

* `flat_atPrime_of_flat_away`: if `M_b` is flat over `B` then so is `M_𝔮` for every prime `𝔮 ∌ b`.
* `flat_away_of_projective`: `M_b` is flat over `B` when `(M_b)` is projective over `B_b`.
* `flat_semilocal`: for `M` finite over `B` with `M_𝔮` flat over `B` for all `𝔮` over `𝔭`, the
  semilocal ring `M_𝔭` is flat over `B`.
* `exists_flat_basicOpen`: (ring form of the open flat locus) there is `b ∉ 𝔭` such that `M_𝔮` is
  flat over `B` for every prime `𝔮` of `M` not containing `b`.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace RamanujanPetersson.IntersectB

section Ring

variable {B M : Type u} [CommRing B] [CommRing M] [Algebra B M]

theorem flat_atPrime_of_flat_away (b : B) (𝔮 : Ideal M) [𝔮.IsPrime]
    (hb : algebraMap B M b ∉ 𝔮)
    (hN : Module.Flat B (Localization (Algebra.algebraMapSubmonoid M (Submonoid.powers b)))) :
    Module.Flat B (Localization.AtPrime 𝔮) := by
  set S := Algebra.algebraMapSubmonoid M (Submonoid.powers b) with hSdef
  have hS : S ≤ 𝔮.primeCompl := by
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    show _ ∉ 𝔮
    rw [map_pow]
    exact fun h => hb (‹𝔮.IsPrime›.mem_of_pow_mem n h)
  letI : Algebra (Localization S) (Localization.AtPrime 𝔮) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ S 𝔮.primeCompl hS
  have : IsScalarTower M (Localization S) (Localization.AtPrime 𝔮) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ S 𝔮.primeCompl hS
  have : IsLocalization (𝔮.primeCompl.map (algebraMap M (Localization S)))
      (Localization.AtPrime 𝔮) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ S 𝔮.primeCompl hS
  have : Module.Flat (Localization S) (Localization.AtPrime 𝔮) :=
    IsLocalization.flat _ (𝔮.primeCompl.map (algebraMap M (Localization S)))
  have : IsScalarTower B (Localization S) (Localization.AtPrime 𝔮) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply B M (Localization S),
        IsScalarTower.algebraMap_apply B M (Localization.AtPrime 𝔮),
        ← IsScalarTower.algebraMap_apply M (Localization S) (Localization.AtPrime 𝔮)]
  exact Module.Flat.trans B (Localization S) (Localization.AtPrime 𝔮)

theorem flat_away_of_projective (b : B)
    [Module.Projective (Localization.Away b) (LocalizedModule.Away b M)] :
    Module.Flat B (Localization (Algebra.algebraMapSubmonoid M (Submonoid.powers b))) := by
  have : Module.Flat B (LocalizedModule.Away b M) :=
    (Module.flat_iff_of_isLocalization (Localization.Away b) (Submonoid.powers b) _).mp
      inferInstance
  have : IsLocalizedModule (Submonoid.powers b) (IsScalarTower.toAlgHom B M
      (Localization (Algebra.algebraMapSubmonoid M (Submonoid.powers b)))).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  exact Module.Flat.of_linearEquiv (IsLocalizedModule.iso (Submonoid.powers b) (IsScalarTower.toAlgHom
    B M (Localization (Algebra.algebraMapSubmonoid M (Submonoid.powers b)))).toLinearMap).symm

theorem flat_semilocal [Module.Finite B M] (𝔭 : Ideal B) [𝔭.IsPrime]
    (h : ∀ (𝔮 : Ideal M) [𝔮.IsPrime], 𝔮.comap (algebraMap B M) = 𝔭 →
      Module.Flat B (Localization.AtPrime 𝔮)) :
    Module.Flat B (Localization (Algebra.algebraMapSubmonoid M 𝔭.primeCompl)) := by
  set Sp := Algebra.algebraMapSubmonoid M 𝔭.primeCompl
  refine Module.flat_of_isLocalized_maximal (Localization Sp) (Localization Sp)
    (fun P _ => Localization.AtPrime P) (fun P _ => Algebra.linearMap _ _) (fun P hP => ?_)
  have hmax : (P.comap (algebraMap (Localization.AtPrime 𝔭) (Localization Sp))).IsMaximal :=
    Ideal.IsMaximal.under (Localization.AtPrime 𝔭) P
  have h𝔮 : (P.comap (algebraMap M (Localization Sp))).comap (algebraMap B M) = 𝔭 := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq B (Localization.AtPrime 𝔭) (Localization Sp),
      ← Ideal.comap_comap, IsLocalRing.eq_maximalIdeal hmax]
    exact Localization.AtPrime.under_maximalIdeal (I := 𝔭)
  have := h _ h𝔮
  exact Module.Flat.of_linearEquiv
    ((IsLocalization.localizationLocalizationAtPrimeIsoLocalization Sp P).restrictScalars
      B).toLinearEquiv.symm

theorem exists_flat_basicOpen [IsNoetherianRing B] [Module.Finite B M] (𝔭 : Ideal B) [𝔭.IsPrime]
    (h : ∀ (𝔮 : Ideal M) [𝔮.IsPrime], 𝔮.comap (algebraMap B M) = 𝔭 →
      Module.Flat B (Localization.AtPrime 𝔮)) :
    ∃ b ∉ 𝔭, ∀ (𝔮 : Ideal M) [𝔮.IsPrime], algebraMap B M b ∉ 𝔮 →
      Module.Flat B (Localization.AtPrime 𝔮) := by
  set Sp := Algebra.algebraMapSubmonoid M 𝔭.primeCompl
  have := Module.finitePresentation_of_finite B M
  have := flat_semilocal 𝔭 h
  have : Module.Flat (Localization.AtPrime 𝔭) (Localization Sp) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime 𝔭) 𝔭.primeCompl _).mpr
      inferInstance
  have : Module.Free (Localization.AtPrime 𝔭) (Localization Sp) :=
    Module.free_of_flat_of_isLocalRing
  have : IsLocalizedModule 𝔭.primeCompl
      (IsScalarTower.toAlgHom B M (Localization Sp)).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  have hmem : (⟨𝔭, inferInstance⟩ : PrimeSpectrum B) ∈ Module.freeLocus B M :=
    (Module.mem_freeLocus_of_isLocalization _ (Localization.AtPrime 𝔭) (Localization Sp)
      (IsScalarTower.toAlgHom B M (Localization Sp)).toLinearMap).mpr inferInstance
  obtain ⟨_, ⟨b, rfl⟩, hb, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hmem
      Module.isOpen_freeLocus
  have := Module.basicOpen_subset_freeLocus_iff.mp hsub
  exact ⟨b, hb, fun 𝔮 _ h𝔮 => flat_atPrime_of_flat_away b 𝔮 h𝔮 (flat_away_of_projective b)⟩

end Ring

section Scheme

theorem isFinite_restrict_of_le {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : Y.Opens} (hUV : U ≤ V)
    [IsFinite (f ∣_ V)] : IsFinite (f ∣_ U) := by
  have hE : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U := by simpa [Scheme.Hom.image_preimage_eq_opensRange_inf]
  have : MorphismProperty.RespectsIso @IsFinite :=
    MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f (_ : IsIso f) => inferInstance
  exact (MorphismProperty.arrow_mk_iso_iff @IsFinite
    (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U) ≪≫ morphismRestrictEq f hE)).mp inferInstance

theorem finite_app_of_isFinite_restrict {X Y : Scheme.{u}} (p : X ⟶ Y) (U : Y.Opens)
    (hU : IsAffineOpen U) [IsFinite (p ∣_ U)] : (p.app U).hom.Finite := by
  have : IsAffine U := hU
  have h := Scheme.Hom.finite_appTop (p ∣_ U)
  change ((p ∣_ U).app ⊤).hom.Finite at h
  rw [morphismRestrict_app'] at h
  rw [Scheme.Hom.app_eq_appLE]
  exact (Scheme.Hom.appLE_congr _ _ (Scheme.Opens.ι_image_top U) (by simp)
    (fun φ => φ.hom.Finite)).mp h

theorem mem_basicOpen_iff_primeIdealOf {Y : Scheme.{u}} {U : Y.Opens} (hU : IsAffineOpen U)
    (y : Y) (hy : y ∈ U) (b : Γ(Y, U)) :
    y ∈ Y.basicOpen b ↔ b ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal := by
  letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hy⟩
  have := hU.isLocalization_stalk ⟨y, hy⟩
  rw [Scheme.mem_basicOpen Y b y hy]
  exact IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk y) _ b

theorem stalkMap_flat_iff {X Y : Scheme.{u}} (p : X ⟶ Y) (U : Y.Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen (p ⁻¹ᵁ U)) (x : X) (hx : p x ∈ U) :
    (p.stalkMap x).hom.Flat ↔
      letI := (p.app U).hom.toAlgebra
      Module.Flat Γ(Y, U) (Localization.AtPrime (hV.primeIdealOf ⟨x, hx⟩).asIdeal) := by
  letI := (p.app U).hom.toAlgebra
  letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨p x, hx⟩
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : p ⁻¹ᵁ U)
  have hlt := hU.isLocalization_stalk ⟨p x, hx⟩
  have hlx := hV.isLocalization_stalk ⟨x, hx⟩
  letI : Algebra (Y.presheaf.stalk (p x)) (X.presheaf.stalk x) := (p.stalkMap x).hom.toAlgebra
  letI : Algebra Γ(Y, U) (X.presheaf.stalk x) :=
    ((p.stalkMap x).hom.comp (Y.presheaf.germ U (p x) hx).hom).toAlgebra
  have : IsScalarTower Γ(Y, U) (Y.presheaf.stalk (p x)) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Γ(Y, U) Γ(X, p ⁻¹ᵁ U) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun r => Scheme.Hom.germ_stalkMap_apply p U x hx r
  change Module.Flat (Y.presheaf.stalk (p x)) (X.presheaf.stalk x) ↔ _
  rw [Module.flat_iff_of_isLocalization (Y.presheaf.stalk (p x))
    (hU.primeIdealOf ⟨p x, hx⟩).asIdeal.primeCompl]
  let e : Localization.AtPrime (hV.primeIdealOf ⟨x, hx⟩).asIdeal ≃ₐ[Γ(X, p ⁻¹ᵁ U)]
      X.presheaf.stalk x :=
    IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _ _
  exact ⟨fun _ => Module.Flat.of_linearEquiv (e.restrictScalars Γ(Y, U)).toLinearEquiv,
    fun _ => Module.Flat.of_linearEquiv (e.restrictScalars Γ(Y, U)).toLinearEquiv.symm⟩

theorem exists_basicOpen_flat_stalk {X Y : Scheme.{u}} (p : X ⟶ Y) (U : Y.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen (p ⁻¹ᵁ U)) (hfin : (p.app U).hom.Finite)
    [IsNoetherianRing Γ(Y, U)] (y : Y) (hy : y ∈ U)
    (hflat : ∀ x, p x = y → (p.stalkMap x).hom.Flat) :
    ∃ b : Γ(Y, U), y ∈ Y.basicOpen b ∧ ∀ x, p x ∈ Y.basicOpen b → (p.stalkMap x).hom.Flat := by
  letI := (p.app U).hom.toAlgebra
  have : Module.Finite Γ(Y, U) Γ(X, p ⁻¹ᵁ U) := hfin
  have hcomap : ∀ x (hx : p x ∈ U), (hV.primeIdealOf ⟨x, hx⟩).asIdeal.comap
      (algebraMap Γ(Y, U) Γ(X, p ⁻¹ᵁ U)) = (hU.primeIdealOf ⟨p x, hx⟩).asIdeal := by
    intro x hx
    have h := IsAffineOpen.comap_primeIdealOf_appLE (f := p) U hU (p ⁻¹ᵁ U) hV le_rfl hx
    rw [Scheme.Hom.appLE_eq_app] at h
    exact congrArg PrimeSpectrum.asIdeal h
  have hsub : ∀ (q q' : PrimeSpectrum Γ(X, p ⁻¹ᵁ U)), q' = q →
      Module.Flat Γ(Y, U) (Localization.AtPrime q'.asIdeal) →
      Module.Flat Γ(Y, U) (Localization.AtPrime q.asIdeal) := by
    rintro _ _ rfl h; exact h
  have hfib : ∀ (𝔮 : Ideal Γ(X, p ⁻¹ᵁ U)) [𝔮.IsPrime],
      𝔮.comap (algebraMap Γ(Y, U) Γ(X, p ⁻¹ᵁ U)) = (hU.primeIdealOf ⟨y, hy⟩).asIdeal →
      Module.Flat Γ(Y, U) (Localization.AtPrime 𝔮) := by
    intro 𝔮 _ h𝔮
    let q : PrimeSpectrum Γ(X, p ⁻¹ᵁ U) := ⟨𝔮, inferInstance⟩
    have hxV : hV.fromSpec q ∈ p ⁻¹ᵁ U := by
      rw [← SetLike.mem_coe, ← hV.range_fromSpec]; exact ⟨q, rfl⟩
    have hq : hV.primeIdealOf ⟨hV.fromSpec q, hxV⟩ = q :=
      hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf ⟨_, hxV⟩)
    have hpx : p (hV.fromSpec q) = y := by
      have h1 := hcomap _ hxV
      rw [hq] at h1
      have h2 : hU.primeIdealOf ⟨p (hV.fromSpec q), hxV⟩ = hU.primeIdealOf ⟨y, hy⟩ :=
        PrimeSpectrum.ext (h1.symm.trans h𝔮)
      have h3 := congrArg hU.fromSpec h2
      rwa [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at h3
    exact hsub q _ hq ((stalkMap_flat_iff p U hU hV _ hxV).mp (hflat _ hpx))
  obtain ⟨b, hb, H⟩ := exists_flat_basicOpen (B := Γ(Y, U)) (M := Γ(X, p ⁻¹ᵁ U))
    (hU.primeIdealOf ⟨y, hy⟩).asIdeal hfib
  refine ⟨b, (mem_basicOpen_iff_primeIdealOf hU y hy b).mpr hb, fun x hx => ?_⟩
  have hxU : p x ∈ U := Y.basicOpen_le b hx
  rw [stalkMap_flat_iff p U hU hV x hxU]
  refine H _ fun hmem => (mem_basicOpen_iff_primeIdealOf hU (p x) hxU b).mp hx ?_
  rw [← hcomap x hxU]
  exact hmem

/-- (B') A proper morphism to a locally Noetherian scheme with a finite fibre at `t` whose stalk
maps over `t` are flat is finite over an open neighbourhood `V` of `t`, with flat stalk maps at
every point over `V`. -/
theorem exists_flat_nbhd {Z T : Scheme.{u}} (p : Z ⟶ T) [IsProper p] [IsLocallyNoetherian T]
    (t : T) (hfin : (p ⁻¹' {t}).Finite) (hflat : ∀ z, p z = t → (p.stalkMap z).hom.Flat) :
    ∃ V : T.Opens, t ∈ V ∧ IsFinite (p ∣_ V) ∧ ∀ z, p z ∈ V → (p.stalkMap z).hom.Flat := by
  obtain ⟨V1, htV1, hV1⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton p t hfin
  obtain ⟨U, hU, htU, hUV1⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens htV1
  have hU' : IsAffineOpen U := hU
  have : IsFinite (p ∣_ U) := isFinite_restrict_of_le p hUV1
  have : IsAffine U := hU'
  have hV : IsAffineOpen (p ⁻¹ᵁ U) := isAffine_of_isAffineHom (p ∣_ U)
  have : IsNoetherianRing Γ(T, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU'⟩
  obtain ⟨b, htb, H⟩ := exists_basicOpen_flat_stalk p U hU' hV
    (finite_app_of_isFinite_restrict p U hU') t htU hflat
  exact ⟨T.basicOpen b, htb, isFinite_restrict_of_le p ((T.basicOpen_le b).trans hUV1), H⟩

end Scheme

section Const

theorem flat_restrict_of_stalk {Z T : Scheme.{u}} (p : Z ⟶ T) (V : T.Opens)
    (H : ∀ z, p z ∈ V → (p.stalkMap z).hom.Flat) : Flat (p ∣_ V) :=
  Flat.of_stalkMap _ fun x =>
    (RingHom.Flat.respectsIso.arrow_mk_iso_iff (morphismRestrictStalkMap p V x)).mpr (H x.1 x.2)

theorem finrank_pullback_eq_restrict {Z T P S : Scheme.{u}} (p : Z ⟶ T) (V : T.Opens)
    [Flat (p ∣_ V)] [IsFinite (p ∣_ V)] (fst : P ⟶ Z) (snd : P ⟶ S) (c : S ⟶ T)
    (h : IsPullback fst snd p c) (hc : Set.range c ⊆ V) (s : S) :
    ∃ a : V.toScheme, snd.finrank s = (p ∣_ V).finrank a := by
  let c' : S ⟶ V.toScheme := IsOpenImmersion.lift V.ι c (by rw [Scheme.Opens.range_ι]; exact hc)
  have hc' : c' ≫ V.ι = c := IsOpenImmersion.lift_fac _ _ _
  have hr := (isPullback_morphismRestrict p V).flip
  let fst' : P ⟶ (p ⁻¹ᵁ V).toScheme :=
    hr.lift fst (snd ≫ c') (by rw [h.w, Category.assoc, hc'])
  have e1 : fst' ≫ (p ⁻¹ᵁ V).ι = fst := hr.lift_fst _ _ _
  have h' : IsPullback fst' snd (p ∣_ V) c' := by
    refine IsPullback.of_right ?_ (hr.lift_snd _ _ _) hr
    rw [e1, hc']
    exact h
  exact ⟨c' s, Scheme.Hom.finrank_of_isPullback fst' snd (p ∣_ V) c' h' s⟩

theorem finrank_restrict_eq {Z T : Scheme.{u}} [IrreducibleSpace T] [IsLocallyNoetherian T]
    (p : Z ⟶ T) (V : T.Opens) [Flat (p ∣_ V)] [IsFinite (p ∣_ V)] (a b : V.toScheme) :
    (p ∣_ V).finrank a = (p ∣_ V).finrank b := by
  have hV : _root_.IsPreconnected (V : Set T) :=
    ((IrreducibleSpace.isIrreducible_univ (X := T)).isPreirreducible.open_subset V.2
      (Set.subset_univ _)).isPreconnected
  have : _root_.PreconnectedSpace V.toScheme := isPreconnected_iff_preconnectedSpace.mp hV
  exact (Scheme.Hom.isLocallyConstant_finrank (p ∣_ V)).apply_eq_of_preconnectedSpace a b

/-- (C') Fibre ranks of a proper family over an irreducible locally Noetherian base agree at two
points with finite fibres and flat stalk maps, read through any base changes concentrated there. -/
theorem finrank_eq_of_fibres {Z T P0 S0 P1 S1 : Scheme.{u}} (p : Z ⟶ T) [IsProper p]
    [IsLocallyNoetherian T] [IrreducibleSpace T] (t0 t1 : T)
    (hfin0 : (p ⁻¹' {t0}).Finite) (hfin1 : (p ⁻¹' {t1}).Finite)
    (hflat0 : ∀ z, p z = t0 → (p.stalkMap z).hom.Flat)
    (hflat1 : ∀ z, p z = t1 → (p.stalkMap z).hom.Flat)
    (fst0 : P0 ⟶ Z) (snd0 : P0 ⟶ S0) (c0 : S0 ⟶ T) (h0 : IsPullback fst0 snd0 p c0)
    (hc0 : ∀ s, c0 s = t0)
    (fst1 : P1 ⟶ Z) (snd1 : P1 ⟶ S1) (c1 : S1 ⟶ T) (h1 : IsPullback fst1 snd1 p c1)
    (hc1 : ∀ s, c1 s = t1) (s0 : S0) (s1 : S1) :
    snd0.finrank s0 = snd1.finrank s1 := by
  obtain ⟨V0, ht0, hfV0, hV0⟩ := exists_flat_nbhd p t0 hfin0 hflat0
  obtain ⟨V1, ht1, hfV1, hV1⟩ := exists_flat_nbhd p t1 hfin1 hflat1
  have := flat_restrict_of_stalk p V0 hV0
  have := flat_restrict_of_stalk p V1 hV1
  obtain ⟨w, hw0, hw1⟩ := nonempty_preirreducible_inter V0.2 V1.2 ⟨t0, ht0⟩ ⟨t1, ht1⟩
  let W : T.Opens := V0 ⊓ V1
  have hwW : w ∈ W := ⟨hw0, hw1⟩
  have hWr : ∀ (V : T.Opens), W ≤ V → Set.range W.ι ⊆ V := fun V hV => by
    rw [Scheme.Opens.range_ι]; exact hV
  obtain ⟨a0, e0⟩ := finrank_pullback_eq_restrict p V0 fst0 snd0 c0 h0
    (by rintro _ ⟨s, rfl⟩; rw [hc0]; exact ht0) s0
  obtain ⟨a1, e1⟩ := finrank_pullback_eq_restrict p V1 fst1 snd1 c1 h1
    (by rintro _ ⟨s, rfl⟩; rw [hc1]; exact ht1) s1
  have hpb := IsPullback.of_hasPullback p W.ι
  obtain ⟨b0, f0⟩ := finrank_pullback_eq_restrict p V0 _ _ _ hpb (hWr V0 inf_le_left)
    (⟨w, hwW⟩ : W)
  obtain ⟨b1, f1⟩ := finrank_pullback_eq_restrict p V1 _ _ _ hpb (hWr V1 inf_le_right)
    (⟨w, hwW⟩ : W)
  rw [e0, e1, finrank_restrict_eq p V0 a0 b0, finrank_restrict_eq p V1 a1 b1, ← f0, ← f1]

end Const

end RamanujanPetersson.IntersectB

theorem solution
    {Z T P₀ S₀ P₁ S₁ : AlgebraicGeometry.Scheme.{u}} (p : Z ⟶ T) [AlgebraicGeometry.IsProper p]
    [AlgebraicGeometry.IsLocallyNoetherian T] [IrreducibleSpace T] (t₀ t₁ : T)
    (hfin₀ : (p ⁻¹' {t₀}).Finite) (hfin₁ : (p ⁻¹' {t₁}).Finite)
    (hflat₀ : ∀ z, p z = t₀ → (p.stalkMap z).hom.Flat)
    (hflat₁ : ∀ z, p z = t₁ → (p.stalkMap z).hom.Flat)
    (fst₀ : P₀ ⟶ Z) (snd₀ : P₀ ⟶ S₀) (c₀ : S₀ ⟶ T) (h₀ : CategoryTheory.IsPullback fst₀ snd₀ p c₀)
    (hc₀ : ∀ s, c₀ s = t₀)
    (fst₁ : P₁ ⟶ Z) (snd₁ : P₁ ⟶ S₁) (c₁ : S₁ ⟶ T) (h₁ : CategoryTheory.IsPullback fst₁ snd₁ p c₁)
    (hc₁ : ∀ s, c₁ s = t₁) (s₀ : S₀) (s₁ : S₁) :
    snd₀.finrank s₀ = snd₁.finrank s₁ := by
  exact RamanujanPetersson.IntersectB.finrank_eq_of_fibres p t₀ t₁ hfin₀ hfin₁ hflat₀ hflat₁
    fst₀ snd₀ c₀ h₀ hc₀ fst₁ snd₁ c₁ h₁ hc₁ s₀ s₁
