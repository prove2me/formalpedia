-- Prove2me | solution 1 for AlgebraicGeometry.existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/3f305a4c-3730-5a40-8bfb-a81f42fe244a

import Mathlib
import Theorems.Thm_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.resLE_comp_ι IsLocallyNoetherian IsOpenImmersion.lift Surjective Scheme.Opens.range_ι Scheme.Hom Scheme.isoSpec_hom isInitialOfIsEmpty ext_of_isAffine IsAffine Spec IsIntegral Scheme ext_of_isDominant Scheme.Hom.appTop isReduced_of_isReduced_stalk Scheme.toSpecΓ_appTop IsOpenImmersion functionField_isFractionRing_of_isAffineOpen germ_injective_of_isIntegral Scheme.Hom.comp_appTop Scheme.openCoverOfIsOpenCover_f isIntegral_of_isOpenImmersion IsReduced IsLocallyNoetherian.component_noetherian exists_isAffineOpen_mem_and_subset isLocallyNoetherian_of_isOpenImmersion isAffineOpen_top ΓSpec.adjunction isIntegral_of_isAffine_of_isDomain Scheme.Cover.glueMorphisms Scheme.Opens.ι_apply ΓSpec_adjunction_homEquiv_eq IsDominant IsAffineOpen Scheme.Hom.preimage_iSup Scheme.Hom.resLE_comp_ι_assoc Scheme.Opens isDominant_iff Scheme.Cover.hom_ext Scheme.Opens.ι_app Scheme.Hom.comp_preimage IsOpenImmersion.lift_fac Scheme.Hom.comp_apply geometrically Scheme.Cover Scheme.ΓSpecIso"
namespace HartogsAffine
p2m_open "AlgebraicGeometry"

section Affine

variable {X : Scheme.{u}} [IsAffine X]

noncomputable def pointOfPrime (p : PrimeSpectrum Γ(X, ⊤)) : (⊤ : X.Opens) :=
  ⟨(isAffineOpen_top X).fromSpec.base p, trivial⟩

theorem primeIdealOf_pointOfPrime (p : PrimeSpectrum Γ(X, ⊤)) :
    (isAffineOpen_top X).primeIdealOf (pointOfPrime p) = p := by
  have h := (isAffineOpen_top X).fromSpec_primeIdealOf (pointOfPrime p)
  change (isAffineOpen_top X).fromSpec.base _ = (isAffineOpen_top X).fromSpec.base p at h
  exact (isAffineOpen_top X).fromSpec.isOpenEmbedding.injective h

scoped instance isLocalization_stalk_pointOfPrime (p : PrimeSpectrum Γ(X, ⊤)) :
    IsLocalization.AtPrime (X.presheaf.stalk (pointOfPrime p).1) p.asIdeal := by
  have := (isAffineOpen_top X).isLocalization_stalk (pointOfPrime p)
  rwa [primeIdealOf_pointOfPrime] at this

theorem ringKrullDim_stalk_pointOfPrime (p : PrimeSpectrum Γ(X, ⊤)) :
    ringKrullDim (X.presheaf.stalk (pointOfPrime p).1) = p.asIdeal.height :=
  IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (X.presheaf.stalk (pointOfPrime p).1)

theorem isIntegrallyClosed_sections [IsDomain Γ(X, ⊤)]
    (h : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) : IsIntegrallyClosed Γ(X, ⊤) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hp
  haveI := h (pointOfPrime ⟨p, hp.isPrime⟩).1
  haveI := isLocalization_stalk_pointOfPrime (X := X) ⟨p, hp.isPrime⟩
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk (pointOfPrime ⟨p, hp.isPrime⟩).1)
      (Localization.AtPrime p)).toRingEquiv

end Affine

section Sections

variable {X : Scheme.{u}} [IsIntegral X]

theorem genericPoint_mem_of_ringKrullDim (V : X.Opens) (hV : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ V) :
    genericPoint X ∈ V := by
  apply hV
  have : ringKrullDim (X.presheaf.stalk (genericPoint X)) = 0 := ringKrullDim_eq_zero_of_field X.functionField
  rw [this]
  exact zero_le_one

theorem restrict_injective (V : X.Opens) (hV : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ V) :
    Function.Injective (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op) := by
  intro a b h
  have hξ := genericPoint_mem_of_ringKrullDim V hV
  apply germ_injective_of_isIntegral X (U := ⊤) (genericPoint X) trivial
  have ha := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : V ≤ ⊤)) (genericPoint X) hξ a
  have hb := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : V ≤ ⊤)) (genericPoint X) hξ b
  rw [← ha, ← hb, h]

variable [IsAffine X]

theorem restrict_surjective [IsLocallyNoetherian X] (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (V : X.Opens) (hV : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ V) :
    Function.Surjective (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op) := by
  intro σ
  have hξ := genericPoint_mem_of_ringKrullDim V hV
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  haveI : IsIntegrallyClosed Γ(X, ⊤) := isIntegrallyClosed_sections hX
  haveI : IsNoetherianRing Γ(X, ⊤) := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  haveI : IsFractionRing Γ(X, ⊤) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)

  let x : X.functionField := X.presheaf.germ V (genericPoint X) hξ σ

  have hx : ∀ (p : Ideal Γ(X, ⊤)) [p.IsPrime], p.height = 1 →
      ∃ r s : Γ(X, ⊤), s ∉ p ∧ x * algebraMap Γ(X, ⊤) X.functionField s = algebraMap Γ(X, ⊤) X.functionField r := by
    intro p _ hp
    let y : (⊤ : X.Opens) := pointOfPrime ⟨p, ‹_›⟩
    haveI := isLocalization_stalk_pointOfPrime (X := X) ⟨p, ‹_›⟩
    have hy : y.1 ∈ V := hV y.1 (by
      rw [show y = pointOfPrime ⟨p, ‹_›⟩ from rfl, ringKrullDim_stalk_pointOfPrime]; exact_mod_cast hp.le)

    obtain ⟨⟨r, s⟩, hrs⟩ :=
      IsLocalization.surj (M := p.primeCompl) (S := X.presheaf.stalk y.1) (X.presheaf.germ V y.1 hy σ)
    refine ⟨r, s, s.2, ?_⟩

    have hspec : genericPoint X ⤳ y.1 := genericPoint_specializes y.1
    have key := congrArg (X.presheaf.stalkSpecializes hspec) hrs
    simp only [map_mul] at key

    have e1 : X.presheaf.stalkSpecializes hspec (X.presheaf.germ V y.1 hy σ) = x :=
      TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    have e2 : ∀ t : Γ(X, ⊤), X.presheaf.stalkSpecializes hspec (algebraMap Γ(X, ⊤) (X.presheaf.stalk y.1) t) =
        algebraMap Γ(X, ⊤) X.functionField t := by
      intro t
      change X.presheaf.stalkSpecializes hspec (X.presheaf.germ ⊤ y.1 y.2 t) =
        X.presheaf.germ ⊤ (genericPoint X) trivial t
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    rw [e1, e2, e2] at key
    exact key
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_forall_height_eq_one X.functionField x hx
  refine ⟨r, ?_⟩
  apply germ_injective_of_isIntegral X (genericPoint X) hξ
  rw [TopCat.Presheaf.germ_res_apply X.presheaf]
  exact hr

theorem appTop_bijective [IsLocallyNoetherian X] (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (V : X.Opens) (hV : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ V) :
    Function.Bijective V.ι.appTop := by
  have heq : V.ι ''ᵁ (V.ι ⁻¹ᵁ ⊤) = V := by simp
  have hV' : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ V.ι ''ᵁ (V.ι ⁻¹ᵁ ⊤) := fun x hx => by
    rw [heq]; exact hV x hx
  rw [Scheme.Hom.appTop, Scheme.Opens.ι_app]
  exact ⟨restrict_injective _ hV', restrict_surjective hX _ hV'⟩

theorem existsUnique_extension [IsLocallyNoetherian X] (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {Y : Scheme.{u}} [IsAffine Y] (V : X.Opens) (hV : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ V)
    (v : (V : Scheme.{u}) ⟶ Y) : ∃! φ : X ⟶ Y, V.ι ≫ φ = v := by
  have hb := appTop_bijective hX V hV
  haveI : Mono V.ι.appTop := ConcreteCategory.mono_of_injective _ hb.1

  have huniq : ∀ φ₁ φ₂ : X ⟶ Y, V.ι ≫ φ₁ = v → V.ι ≫ φ₂ = v → φ₁ = φ₂ := by
    intro φ₁ φ₂ h₁ h₂
    apply ext_of_isAffine
    rw [← cancel_mono V.ι.appTop, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, h₁, h₂]

  let ρ : Γ(X, ⊤) ≅ Γ(V, ⊤) := (RingEquiv.ofBijective V.ι.appTop.hom hb).toCommRingCatIso
  have hρ : ρ.hom = V.ι.appTop := rfl
  let ψ : Γ(Y, ⊤) ⟶ Γ(X, ⊤) := v.appTop ≫ ρ.inv
  let φ₀ : X ⟶ Spec Γ(Y, ⊤) := ΓSpec.adjunction.homEquiv X (op Γ(Y, ⊤)) ψ.op
  have hφ₀ : φ₀.appTop = (Scheme.ΓSpecIso Γ(Y, ⊤)).hom ≫ ψ := ΓSpec_adjunction_homEquiv_eq ψ
  have hext : V.ι ≫ φ₀ ≫ Y.isoSpec.inv = v := by
    rw [← Category.assoc, Iso.comp_inv_eq]
    apply ext_of_isAffine
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, hφ₀, Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop,
      Category.assoc, Category.assoc, ← hρ, Iso.inv_hom_id, Category.comp_id]
  exact ⟨φ₀ ≫ Y.isoSpec.inv, hext, fun φ' hφ' => huniq _ _ hφ' hext⟩

end Sections

section LocallyIntegral

open IsLocalization in

theorem exists_isDomain_away {B : Type*} [CommRing B] [IsNoetherianRing B] [_root_.IsReduced B]
    (p : Ideal B) [p.IsPrime] (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] [IsDomain Bp] :
    ∃ f : B, f ∉ p ∧ ∀ (C : Type*) [CommRing C] [Algebra B C] [IsLocalization.Away f C], IsDomain C := by
  classical

  let e := IsLocalization.AtPrime.orderIsoOfPrime Bp p
  let q₀ : Ideal B := (e ⟨⊥, Ideal.isPrime_bot⟩).1
  have hq₀p : q₀ ≤ p := (e ⟨⊥, Ideal.isPrime_bot⟩).2.2
  haveI hq₀ : q₀.IsPrime := (e ⟨⊥, Ideal.isPrime_bot⟩).2.1
  have hleast : ∀ q : Ideal B, q.IsPrime → q ≤ p → q₀ ≤ q := by
    intro q hq hqp
    have : e ⟨⊥, Ideal.isPrime_bot⟩ ≤ e (e.symm ⟨q, hq, hqp⟩) :=
      e.monotone (show (⟨⊥, Ideal.isPrime_bot⟩ : {P : Ideal Bp // P.IsPrime}) ≤ e.symm ⟨q, hq, hqp⟩ from
        (bot_le : (⊥ : Ideal Bp) ≤ (e.symm ⟨q, hq, hqp⟩).1))
    rw [OrderIso.apply_symm_apply] at this
    exact this

  have hpick : ∀ q ∈ minimalPrimes B, q ≠ q₀ → ∃ a ∈ q, a ∉ p := by
    intro q hq hne
    by_contra hcon
    push Not at hcon
    have hqp : q ≤ p := fun a ha => hcon a ha
    have h1 : q₀ ≤ q := hleast q hq.1.1 hqp
    exact hne (le_antisymm (hq.2 ⟨hq₀, bot_le⟩ h1) h1)
  choose! a ha using hpick
  let S : Finset (Ideal B) := (minimalPrimes.finite_of_isNoetherianRing B).toFinset.erase q₀
  let f : B := ∏ q ∈ S, a q
  have hS : ∀ q ∈ S, q ∈ minimalPrimes B ∧ q ≠ q₀ := fun q hq => by
    simpa [S, and_comm] using hq
  have hfp : f ∉ p := by
    rw [Ideal.IsPrime.prod_mem_iff]
    push Not
    exact fun q hq => (ha q (hS q hq).1 (hS q hq).2).2
  have hfq : ∀ q ∈ minimalPrimes B, q ≠ q₀ → f ∈ q := by
    intro q hq hne
    have hqS : q ∈ S := by simp [S, hq, hne]
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem a hqS
    rw [show f = a q * c from hc]
    exact Ideal.mul_mem_right _ _ (ha q hq hne).1

  have hkill : ∀ b : B, algebraMap B Bp b = 0 → f * b = 0 := by
    intro b hb
    obtain ⟨⟨s, hs⟩, hsb⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl Bp b).mp hb
    have hbq₀ : b ∈ q₀ := by
      have : s * b ∈ q₀ := by rw [hsb]; exact q₀.zero_mem
      exact (hq₀.mem_or_mem this).resolve_left fun h => hs (hq₀p h)

    have hmem : ∀ q ∈ minimalPrimes B, f * b ∈ q := by
      intro q hq
      by_cases hne : q = q₀
      · subst hne; exact Ideal.mul_mem_left _ _ hbq₀
      · exact Ideal.mul_mem_right _ _ (hfq q hq hne)
    have hnil : f * b ∈ nilradical B := by
      rw [nilradical, ← Ideal.sInf_minimalPrimes]
      exact Ideal.mem_sInf.mpr fun q hq => hmem q hq
    simpa [nilradical_eq_zero, Ideal.zero_eq_bot, Ideal.mem_bot] using hnil
  refine ⟨f, hfp, fun C _ _ _ => ?_⟩

  have hunit : ∀ y : Submonoid.powers f, IsUnit (algebraMap B Bp y) := by
    rintro ⟨y, n, rfl⟩
    apply IsLocalization.map_units Bp (⟨f ^ n, ?_⟩ : p.primeCompl)
    exact fun h => hfp (Ideal.IsPrime.mem_of_pow_mem ‹_› n h)
  let φ : C →+* Bp := IsLocalization.lift (M := Submonoid.powers f) hunit
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) z
    rw [IsLocalization.lift_mk', Units.mul_left_eq_zero] at hz
    have hfb := hkill b hz
    rw [IsLocalization.mk'_eq_zero_iff]
    exact ⟨⟨f, 1, pow_one f⟩, hfb⟩
  haveI : Nontrivial C := ⟨⟨0, 1, fun h => zero_ne_one (α := Bp) (by simpa using congrArg φ h)⟩⟩
  haveI : NoZeroDivisors C := Function.Injective.noZeroDivisors φ hinj (map_zero φ) (fun x y => map_mul φ x y)
  exact NoZeroDivisors.to_isDomain C

end LocallyIntegral

section Wrapper

variable {T : Scheme.{u}} [IsLocallyNoetherian T]

theorem exists_isIntegral_affineOpen (hT : ∀ x : T, IsDomain (T.presheaf.stalk x)) (x : T) :
    ∃ U : T.Opens, x ∈ U ∧ IsAffineOpen U ∧ IsIntegral (U : Scheme.{u}) := by
  obtain ⟨U₀, hU₀, hxU₀, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ x)
  haveI : IsNoetherianRing Γ(T, U₀) := IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩
  haveI : ∀ y : T, _root_.IsReduced (T.presheaf.stalk y) := fun y => inferInstance
  haveI : IsReduced T := isReduced_of_isReduced_stalk T
  obtain ⟨x', hx'⟩ : ∃ x' : U₀, x'.1 = x := ⟨⟨x, hxU₀⟩, rfl⟩
  haveI := hU₀.isLocalization_stalk x'
  haveI : IsDomain (T.presheaf.stalk x'.1) := hT x'.1
  obtain ⟨f, hfp, hdom⟩ := exists_isDomain_away (hU₀.primeIdealOf x').asIdeal (T.presheaf.stalk x'.1)
  have hxf : x ∈ T.basicOpen f := by
    have h1 : hU₀.primeIdealOf x' ∈ hU₀.fromSpec ⁻¹ᵁ T.basicOpen f := by
      rw [hU₀.fromSpec_preimage_basicOpen]
      exact (PrimeSpectrum.mem_basicOpen _ _).mpr hfp
    have h2 : hU₀.fromSpec.base (hU₀.primeIdealOf x') ∈ T.basicOpen f := h1
    rwa [hU₀.fromSpec_primeIdealOf, hx'] at h2
  refine ⟨T.basicOpen f, hxf, hU₀.basicOpen f, ?_⟩
  · haveI : IsAffine (T.basicOpen f : Scheme.{u}) := hU₀.basicOpen f
    haveI : Nonempty (T.basicOpen f : Scheme.{u}) := ⟨⟨x, hxf⟩⟩
    haveI := hU₀.isLocalization_basicOpen f
    haveI : IsDomain Γ(T, T.basicOpen f) := hdom _
    haveI : IsDomain Γ(T.basicOpen f, ⊤) :=
      MulEquiv.isDomain Γ(T, T.basicOpen f) (T.basicOpen f).topIso.commRingCatIsoToRingEquiv.toMulEquiv
    exact isIntegral_of_isAffine_of_isDomain _

end Wrapper

section Glue

variable {T : Scheme.{u}}

theorem hyp_restrict (hT : ∀ x : T, IsDomain (T.presheaf.stalk x) ∧ IsIntegrallyClosed (T.presheaf.stalk x))
    (V : T.Opens) (hV : ∀ x : T, ringKrullDim (T.presheaf.stalk x) ≤ 1 → x ∈ V) (U : T.Opens) :
    (∀ y : (U : Scheme.{u}), IsIntegrallyClosed ((U : Scheme.{u}).presheaf.stalk y)) ∧
    (∀ y : (U : Scheme.{u}), ringKrullDim ((U : Scheme.{u}).presheaf.stalk y) ≤ 1 → y ∈ U.ι ⁻¹ᵁ V) := by
  constructor
  · intro y
    haveI := (hT y.1).2
    exact IsIntegrallyClosed.of_equiv (U.stalkIso y).commRingCatIsoToRingEquiv.symm
  · intro y hy
    change U.ι.base y ∈ V
    rw [Scheme.Opens.ι_apply]
    apply hV
    rwa [← ringKrullDim_eq_of_ringEquiv (U.stalkIso y).commRingCatIsoToRingEquiv]

theorem exists_piece [IsLocallyNoetherian T]
    (hT : ∀ x : T, IsDomain (T.presheaf.stalk x) ∧ IsIntegrallyClosed (T.presheaf.stalk x))
    {Y : Scheme.{u}} [IsAffine Y] (V : T.Opens) (hV : ∀ x : T, ringKrullDim (T.presheaf.stalk x) ≤ 1 → x ∈ V)
    (v : (V : Scheme.{u}) ⟶ Y) (U : T.Opens) (hU : IsAffineOpen U) [IsIntegral (U : Scheme.{u})] :
    ∃! φ : (U : Scheme.{u}) ⟶ Y, (U.ι ⁻¹ᵁ V).ι ≫ φ = U.ι.resLE V (U.ι ⁻¹ᵁ V) le_rfl ≫ v := by
  haveI : IsAffine (U : Scheme.{u}) := hU
  haveI : IsLocallyNoetherian (U : Scheme.{u}) := isLocallyNoetherian_of_isOpenImmersion U.ι
  exact existsUnique_extension (hyp_restrict hT V hV U).1 (U.ι ⁻¹ᵁ V) (hyp_restrict hT V hV U).2 _

theorem ext_of_agree {P Y : Scheme.{u}} [IsIntegral P] [IsAffine Y] (W : P.Opens) (hW : (W : Set P).Nonempty)
    (g₁ g₂ : P ⟶ Y) (h : W.ι ≫ g₁ = W.ι ≫ g₂) : g₁ = g₂ := by
  haveI : IsDominant W.ι := by
    rw [isDominant_iff, DenseRange, Scheme.Opens.range_ι]
    exact W.2.dense hW
  exact ext_of_isDominant W.ι h

end Glue

section Main

theorem hartogs {T Y : Scheme.{u}} [IsLocallyNoetherian T]
    (hT : ∀ x : T, IsDomain (T.presheaf.stalk x) ∧ IsIntegrallyClosed (T.presheaf.stalk x))
    [IsAffine Y] (V : T.Opens) (hV : ∀ x : T, ringKrullDim (T.presheaf.stalk x) ≤ 1 → x ∈ V)
    (v : (V : Scheme.{u}) ⟶ Y) : ∃! φ : T ⟶ Y, V.ι ≫ φ = v := by
  classical

  let I := {U : T.Opens // IsAffineOpen U ∧ IsIntegral (U : Scheme.{u})}
  let U : I → T.Opens := fun i => i.1
  have hcov : TopologicalSpace.IsOpenCover U := by
    refine .mk (top_le_iff.mp fun x _ => ?_)
    obtain ⟨W, hxW, hW, hint⟩ := exists_isIntegral_affineOpen (fun x => (hT x).1) x
    exact Opens.mem_iSup.mpr ⟨⟨W, hW, hint⟩, hxW⟩
  let 𝒰 : T.OpenCover := T.openCoverOfIsOpenCover U hcov

  have hpiece : ∀ i : I, ∃! φ : (U i : Scheme.{u}) ⟶ Y,
      ((U i).ι ⁻¹ᵁ V).ι ≫ φ = (U i).ι.resLE V ((U i).ι ⁻¹ᵁ V) le_rfl ≫ v := fun i => by
    haveI := i.2.2
    exact exists_piece hT V hV v (U i) i.2.1
  choose φ hφ using fun i => (hpiece i).exists

  have hrestr : ∀ (ψ : T ⟶ Y), V.ι ≫ ψ = v → ∀ i : I,
      ((U i).ι ⁻¹ᵁ V).ι ≫ ((U i).ι ≫ ψ) = (U i).ι.resLE V ((U i).ι ⁻¹ᵁ V) le_rfl ≫ v := by
    intro ψ hψ i
    rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι _ le_rfl, Category.assoc, hψ]

  have huniq : ∀ ψ₁ ψ₂ : T ⟶ Y, V.ι ≫ ψ₁ = v → V.ι ≫ ψ₂ = v → ψ₁ = ψ₂ := by
    intro ψ₁ ψ₂ h₁ h₂
    apply Scheme.Cover.hom_ext 𝒰
    intro i
    change (U i).ι ≫ ψ₁ = (U i).ι ≫ ψ₂
    exact (hpiece i).unique (hrestr ψ₁ h₁ i) (hrestr ψ₂ h₂ i)

  have hcompat : ∀ i j : I, pullback.fst (𝒰.f i) (𝒰.f j) ≫ φ i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ φ j := by
    intro i j
    change pullback.fst (U i).ι (U j).ι ≫ φ i = pullback.snd (U i).ι (U j).ι ≫ φ j
    rcases isEmpty_or_nonempty ↥(pullback (U i).ι (U j).ι) with hP | hP
    · exact (isInitialOfIsEmpty (X := pullback (U i).ι (U j).ι)).hom_ext _ _
    haveI := i.2.2
    haveI := j.2.2
    haveI : IsIntegral (pullback (U i).ι (U j).ι) := isIntegral_of_isOpenImmersion (pullback.fst (U i).ι (U j).ι)
    let W : (pullback (U i).ι (U j).ι).Opens := pullback.fst (U i).ι (U j).ι ⁻¹ᵁ ((U i).ι ⁻¹ᵁ V)
    have hWj : W ≤ pullback.snd (U i).ι (U j).ι ⁻¹ᵁ ((U j).ι ⁻¹ᵁ V) := by
      change pullback.fst (U i).ι (U j).ι ⁻¹ᵁ ((U i).ι ⁻¹ᵁ V) ≤ _
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]

    have hW : (W : Set ↥(pullback (U i).ι (U j).ι)).Nonempty := by
      let P := pullback (U i).ι (U j).ι
      refine ⟨genericPoint P, ?_⟩
      let g := pullback.fst (U i).ι (U j).ι ≫ (U i).ι
      change genericPoint P ∈ pullback.fst (U i).ι (U j).ι ⁻¹ᵁ ((U i).ι ⁻¹ᵁ V)
      rw [← Scheme.Hom.comp_preimage]
      change g (genericPoint P) ∈ V
      apply hV
      have e : T.presheaf.stalk (g (genericPoint P)) ≃+* P.presheaf.stalk (genericPoint P) :=
        (asIso (g.stalkMap (genericPoint P))).commRingCatIsoToRingEquiv
      rw [ringKrullDim_eq_of_ringEquiv e]
      have : ringKrullDim (P.presheaf.stalk (genericPoint P)) = 0 := ringKrullDim_eq_zero_of_field P.functionField
      rw [this]
      exact zero_le_one
    have l : W.ι ≫ pullback.fst (U i).ι (U j).ι ≫ φ i =
        (pullback.fst (U i).ι (U j).ι).resLE ((U i).ι ⁻¹ᵁ V) W le_rfl ≫
          (U i).ι.resLE V ((U i).ι ⁻¹ᵁ V) le_rfl ≫ v := by
      rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι _ le_rfl, Category.assoc, hφ i]
    have r : W.ι ≫ pullback.snd (U i).ι (U j).ι ≫ φ j =
        (pullback.snd (U i).ι (U j).ι).resLE ((U j).ι ⁻¹ᵁ V) W hWj ≫
          (U j).ι.resLE V ((U j).ι ⁻¹ᵁ V) le_rfl ≫ v := by
      rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι _ hWj, Category.assoc, hφ j]
    have m : (pullback.fst (U i).ι (U j).ι).resLE ((U i).ι ⁻¹ᵁ V) W le_rfl ≫
          (U i).ι.resLE V ((U i).ι ⁻¹ᵁ V) le_rfl =
        (pullback.snd (U i).ι (U j).ι).resLE ((U j).ι ⁻¹ᵁ V) W hWj ≫
          (U j).ι.resLE V ((U j).ι ⁻¹ᵁ V) le_rfl := by
      rw [← cancel_mono V.ι]
      simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc]
      rw [pullback.condition]
    apply ext_of_agree W hW
    rw [l, r, ← Category.assoc, m, Category.assoc]

  have hglue : V.ι ≫ 𝒰.glueMorphisms φ hcompat = v := by
    have hVcov : TopologicalSpace.IsOpenCover (fun i : I => V.ι ⁻¹ᵁ U i) := by
      refine .mk ?_
      rw [← Scheme.Hom.preimage_iSup, hcov.iSup_eq_top]
      exact Opens.map_top _
    apply Scheme.Cover.hom_ext ((V : Scheme.{u}).openCoverOfIsOpenCover _ hVcov)
    intro i
    rw [Scheme.openCoverOfIsOpenCover_f]
    let κ := V.ι.resLE (U i) (V.ι ⁻¹ᵁ U i) le_rfl
    have hκ : κ ≫ (U i).ι = (V.ι ⁻¹ᵁ U i).ι ≫ V.ι := Scheme.Hom.resLE_comp_ι _ _
    have hrange : Set.range κ ⊆ Set.range ((U i).ι ⁻¹ᵁ V).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      change (U i).ι (κ y) ∈ V
      rw [← Scheme.Hom.comp_apply, hκ, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
      exact ((V.ι ⁻¹ᵁ U i).ι y).2
    let g := IsOpenImmersion.lift ((U i).ι ⁻¹ᵁ V).ι κ hrange
    have hg : g ≫ ((U i).ι ⁻¹ᵁ V).ι = κ := IsOpenImmersion.lift_fac _ _ _
    have hg' : g ≫ (U i).ι.resLE V ((U i).ι ⁻¹ᵁ V) le_rfl = (V.ι ⁻¹ᵁ U i).ι := by
      rw [← cancel_mono V.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, hg, hκ]
    have hιg : (U i).ι ≫ 𝒰.glueMorphisms φ hcompat = φ i := by
      have := 𝒰.ι_glueMorphisms φ hcompat i
      rwa [Scheme.openCoverOfIsOpenCover_f] at this
    calc (V.ι ⁻¹ᵁ U i).ι ≫ V.ι ≫ 𝒰.glueMorphisms φ hcompat
        = κ ≫ (U i).ι ≫ 𝒰.glueMorphisms φ hcompat := by rw [← Category.assoc, ← hκ, Category.assoc]
      _ = κ ≫ φ i := by rw [hιg]
      _ = g ≫ ((U i).ι ⁻¹ᵁ V).ι ≫ φ i := by rw [← Category.assoc, hg]
      _ = g ≫ (U i).ι.resLE V ((U i).ι ⁻¹ᵁ V) le_rfl ≫ v := by rw [hφ i]
      _ = (V.ι ⁻¹ᵁ U i).ι ≫ v := by rw [← Category.assoc, hg']
  exact ⟨𝒰.glueMorphisms φ hcompat, hglue, fun ψ hψ => huniq _ _ hψ hglue⟩

end Main

end AlgebraicGeometry.HartogsAffine
p2m_reactivate "P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry.HartogsAffine"
p2m_reactivate "P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry"

theorem solution
    {T Y : Scheme.{u}} [IsLocallyNoetherian T]
    (hT : ∀ x : T, IsDomain (T.presheaf.stalk x) ∧ IsIntegrallyClosed (T.presheaf.stalk x))
    [IsAffine Y] (V : T.Opens) (hV : ∀ x : T, ringKrullDim (T.presheaf.stalk x) ≤ 1 → x ∈ V)
    (v : (V : Scheme.{u}) ⟶ Y) :
    ∃! φ : T ⟶ Y, V.ι ≫ φ = v :=
  AlgebraicGeometry.HartogsAffine.hartogs hT V hV v

end S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk
end P2MW
export P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk (solution)
