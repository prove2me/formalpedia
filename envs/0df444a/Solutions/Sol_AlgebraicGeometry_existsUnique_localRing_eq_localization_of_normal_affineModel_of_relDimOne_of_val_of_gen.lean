-- Prove2me | solution 1 for AlgebraicGeometry.existsUnique_localRing_eq_localization_of_normal_affineModel_of_relDimOne_of_val_of_gen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/b69b3f12-0857-551e-bc99-97cdd92283c8

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicGeometry_exists_localRing_eq_localization_of_normal_affineModel_of_map_maximalIdeal_le
import Theorems.Thm_AlgebraicGeometry_Scheme_eq_of_forall_mem_valuationSubring_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_mem_smoothLocus_iff_formallySmooth_of_ringEquiv_stalk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_existsUnique_localRing_eq_localization_of_normal_affineModel_of_relDimOne_of_val_of_gen

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve IsLocalRing

namespace L1BLO

set_option maxHeartbeats 3200000 in

theorem eq_of_localRing_eq {O : Type} [CommRing O] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of O)) [IsSeparated f]
    {F : Type} [Field F] (φ : F ≃+* X.functionField) (x x' : X)
    (h : SemistableModel.localRing X φ x' = SemistableModel.localRing X φ x) : x' = x := by
  classical

  let ex : ∀ z : X, X.presheaf.stalk z →+* F := fun z =>
    (φ.symm : X.functionField ≃+* F).toRingHom.comp (algebraMap (X.presheaf.stalk z) X.functionField)
  have hmem : ∀ (z : X) (g : X.presheaf.stalk z), ex z g ∈ SemistableModel.localRing X φ z := fun z g => ⟨g, rfl⟩
  have hex_inj : ∀ z : X, Function.Injective (ex z) := fun z =>
    φ.symm.injective.comp (IsFractionRing.injective (X.presheaf.stalk z) X.functionField)
  let ψ : ∀ z : X, X.presheaf.stalk z →+* ↥(SemistableModel.localRing X φ z) := fun z => (ex z).codRestrict _ (hmem z)
  have hψbij : ∀ z : X, Function.Bijective (ψ z) := fun z =>
    ⟨fun a b hab => hex_inj z (congrArg Subtype.val hab), by rintro ⟨_, g, rfl⟩; exact ⟨g, rfl⟩⟩
  haveI hloc : ∀ z : X, IsLocalRing ↥(SemistableModel.localRing X φ z) := fun z =>
    IsLocalRing.of_surjective' (ψ z) (hψbij z).2

  let R : LocalSubring F := LocalSubring.mk (SemistableModel.localRing X φ x)
  obtain ⟨W, hW⟩ := R.exists_le_valuationSubring
  obtain ⟨hRW, hlocRW⟩ := LocalSubring.le_def.mp hW

  let V : ValuationSubring X.functionField := W.comap (φ.symm : X.functionField ≃+* F).toRingHom
  have hV : ∀ t : X.functionField, t ∈ V ↔ φ.symm t ∈ W := fun t => Iff.rfl

  have key : ∀ z : X, SemistableModel.localRing X φ z = SemistableModel.localRing X φ x →
      (∀ s : X.presheaf.stalk z, algebraMap (X.presheaf.stalk z) X.functionField s ∈ V) ∧
      (∀ s ∈ maximalIdeal (X.presheaf.stalk z),
        algebraMap (X.presheaf.stalk z) X.functionField s ∈ V.nonunits) := by
    intro z hz
    refine ⟨fun s => ?_, fun s hs => ?_⟩
    · rw [hV]
      apply hRW
      show ex z s ∈ SemistableModel.localRing X φ x
      rw [← hz]; exact hmem z s
    ·
      have hsR : ex z s ∈ SemistableModel.localRing X φ x := by rw [← hz]; exact hmem z s
      have hnu : (⟨ex z s, hsR⟩ : ↥(SemistableModel.localRing X φ x)) ∈ maximalIdeal _ := by
        rw [mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        apply (mem_maximalIdeal _).mp hs
        have hu' : IsUnit (ψ z s) := by
          obtain ⟨u, hu1⟩ := hu.exists_right_inv
          have huz : (u : F) ∈ SemistableModel.localRing X φ z := by rw [hz]; exact u.2
          refine IsUnit.of_mul_eq_one (b := ⟨u, huz⟩) (Subtype.ext ?_)
          have := congrArg Subtype.val hu1
          exact this
        let e : X.presheaf.stalk z ≃+* ↥(SemistableModel.localRing X φ z) := RingEquiv.ofBijective (ψ z) (hψbij z)
        exact (isUnit_map_iff e s).mp hu'
      have hWmax : (⟨ex z s, hRW hsR⟩ : ↥W) ∈ maximalIdeal ↥W := by
        rw [mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        have hu2 : IsUnit (Subring.inclusion hRW ⟨ex z s, hsR⟩) := hu
        exact ((mem_maximalIdeal _).mp hnu) (hlocRW.map_nonunit _ hu2)
      have hWnu : ex z s ∈ W.nonunits :=
        ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨hRW hsR, hWmax⟩
      rw [ValuationSubring.mem_nonunits_iff_or] at hWnu ⊢
      rcases hWnu with h0 | hinv
      · left
        have : φ.symm (algebraMap (X.presheaf.stalk z) X.functionField s) = 0 := h0
        exact (map_eq_zero_iff (φ.symm : X.functionField ≃+* F) φ.symm.injective).mp this
      · right
        intro hmemV
        apply hinv
        have : φ.symm ((algebraMap (X.presheaf.stalk z) X.functionField s)⁻¹) ∈ W := hmemV
        rwa [map_inv₀] at this
  obtain ⟨h1, h1'⟩ := key x' h
  obtain ⟨h2, h2'⟩ := key x rfl
  exact AlgebraicGeometry.Scheme.eq_of_forall_mem_valuationSubring_of_isSeparated f V x' x h1 h1' h2 h2'

end L1BLO

open CategoryTheory AlgebraicGeometry AlgebraicCurve IsLocalRing

namespace L1BLO

theorem algebraMap_germ_appTop {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of R)) (y : X) (a : R) :
    algebraMap (X.presheaf.stalk y) X.functionField
      ((X.presheaf.germ ⊤ y trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a))) =
    SemistableModel.baseToFunctionField f a := by
  unfold SemistableModel.baseToFunctionField
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply,
    TopCat.Presheaf.germ_stalkSpecializes]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem mem_smoothLocus_iff_of_localRing_eq
    {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation f]
    {F : Type} [Field F] [Algebra R F] (φ : F ≃+* X.functionField)
    (hφ : ∀ a : R, φ (algebraMap R F a) = SemistableModel.baseToFunctionField f a)
    (B : Subalgebra R F) (𝔭 : Ideal ↥B) [𝔭.IsPrime] (x : X)
    (hx : ∀ g : F, g ∈ SemistableModel.localRing X φ x ↔ ∃ b c : ↥B, c ∉ 𝔭 ∧ g * (c : F) = (b : F)) :
    x ∈ f.smoothLocus ↔ (algebraMap R (Localization.AtPrime 𝔭)).FormallySmooth := by
  classical

  let ex : X.presheaf.stalk x →+* F :=
    (φ.symm : X.functionField ≃+* F).toRingHom.comp (algebraMap (X.presheaf.stalk x) X.functionField)
  have hmem : ∀ g : X.presheaf.stalk x, ex g ∈ SemistableModel.localRing X φ x := fun g => ⟨g, rfl⟩
  have hex_inj : Function.Injective ex :=
    φ.symm.injective.comp (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)
  let ψ : X.presheaf.stalk x →+* ↥(SemistableModel.localRing X φ x) := ex.codRestrict _ hmem
  have hψbij : Function.Bijective ψ :=
    ⟨fun a b hab => hex_inj (congrArg Subtype.val hab), by rintro ⟨_, g, rfl⟩; exact ⟨g, rfl⟩⟩
  let eψ : X.presheaf.stalk x ≃+* ↥(SemistableModel.localRing X φ x) := RingEquiv.ofBijective ψ hψbij

  have hc0 : ∀ c : ↥B, c ∉ 𝔭 → (c : F) ≠ 0 := fun c hc h0 => hc (by
    have : c = 0 := Subtype.ext h0
    rw [this]; exact 𝔭.zero_mem)
  have hBmem : ∀ b : ↥B, (b : F) ∈ SemistableModel.localRing X φ x := fun b =>
    (hx b).mpr ⟨b, 1, fun h => (Ideal.ne_top_iff_one 𝔭).mp (Ideal.IsPrime.ne_top ‹_›) h, by simp⟩
  let jB : ↥B →+* ↥(SemistableModel.localRing X φ x) :=
    { toFun := fun b => ⟨b, hBmem b⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  letI algBO : Algebra ↥B ↥(SemistableModel.localRing X φ x) := jB.toAlgebra
  haveI : IsLocalization.AtPrime ↥(SemistableModel.localRing X φ x) 𝔭 := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨c, hc⟩
      have hc' : c ∉ 𝔭 := hc
      have hinv : (c : F)⁻¹ ∈ SemistableModel.localRing X φ x :=
        (hx _).mpr ⟨1, c, hc', by rw [inv_mul_cancel₀ (hc0 c hc')]; simp⟩
      refine IsUnit.of_mul_eq_one (b := ⟨(c : F)⁻¹, hinv⟩) (Subtype.ext ?_)
      show (c : F) * (c : F)⁻¹ = 1
      exact mul_inv_cancel₀ (hc0 c hc')
    · intro z
      obtain ⟨b, c, hc, hz⟩ := (hx z).mp z.2
      refine ⟨⟨b, ⟨c, hc⟩⟩, Subtype.ext ?_⟩
      show (z : F) * (c : F) = (b : F)
      exact hz
    · intro b b' h
      have : (b : F) = (b' : F) := by
        have h2 := congrArg (fun z : ↥(SemistableModel.localRing X φ x) => (z : F)) h
        exact h2
      exact ⟨1, by rw [Subtype.ext this]⟩
  let eBO : Localization.AtPrime 𝔭 ≃ₐ[↥B] ↥(SemistableModel.localRing X φ x) :=
    IsLocalization.algEquiv 𝔭.primeCompl _ _
  let e : X.presheaf.stalk x ≃+* Localization.AtPrime 𝔭 := eψ.trans eBO.symm.toRingEquiv
  have he : ∀ a : R, e ((X.presheaf.germ ⊤ x trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))) =
      algebraMap R (Localization.AtPrime 𝔭) a := by
    intro a
    have h1 : eψ ((X.presheaf.germ ⊤ x trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))) =
        algebraMap ↥B ↥(SemistableModel.localRing X φ x) (algebraMap R ↥B a) := by
      apply Subtype.ext
      show φ.symm (algebraMap (X.presheaf.stalk x) X.functionField _) = ((algebraMap R ↥B a : ↥B) : F)
      rw [algebraMap_germ_appTop f x a, ← hφ, Subalgebra.coe_algebraMap]
      exact φ.symm_apply_apply _
    show eBO.symm (eψ _) = _
    rw [h1, AlgEquiv.commutes, IsScalarTower.algebraMap_apply R ↥B (Localization.AtPrime 𝔭)]
  rw [AlgebraicGeometry.mem_smoothLocus_iff_formallySmooth_of_ringEquiv_stalk f x e he,
    RingHom.formallySmooth_algebraMap]

end L1BLO

open CategoryTheory AlgebraicGeometry AlgebraicCurve IsLocalRing

namespace L1BSpec

variable {F : Type} [Field F] (X : Scheme.{0}) [IsIntegral X] (φ : F ≃+* X.functionField)

noncomputable def ex (z : X) : X.presheaf.stalk z →+* F :=
  (φ.symm : X.functionField ≃+* F).toRingHom.comp (algebraMap (X.presheaf.stalk z) X.functionField)

theorem ex_injective (z : X) : Function.Injective (ex X φ z) :=
  φ.symm.injective.comp (IsFractionRing.injective (X.presheaf.stalk z) X.functionField)

theorem mem_localRing_iff (z : X) (f : F) : f ∈ SemistableModel.localRing X φ z ↔ ∃ g, ex X φ z g = f := by
  show f ∈ RingHom.range _ ↔ _; rw [RingHom.mem_range]; rfl

theorem ex_mem (z : X) (g : X.presheaf.stalk z) : ex X φ z g ∈ SemistableModel.localRing X φ z :=
  (mem_localRing_iff X φ z _).mpr ⟨g, rfl⟩

noncomputable def ψ (z : X) : X.presheaf.stalk z →+* ↥(SemistableModel.localRing X φ z) :=
  (ex X φ z).codRestrict _ (ex_mem X φ z)

theorem ψ_bijective (z : X) : Function.Bijective (ψ X φ z) :=
  ⟨fun a b h => ex_injective X φ z (congrArg Subtype.val h), by
    rintro ⟨f, hf⟩; obtain ⟨g, rfl⟩ := (mem_localRing_iff X φ z f).mp hf; exact ⟨g, rfl⟩⟩

set_option maxHeartbeats 6400000 in

theorem exists_specializes_localRing_iff (x : X) (𝔭 : Ideal ↥(SemistableModel.localRing X φ x)) [𝔭.IsPrime] :
    ∃ y : X, y ⤳ x ∧ ∀ f : F, f ∈ SemistableModel.localRing X φ y ↔
      ∃ a b : ↥(SemistableModel.localRing X φ x), b ∉ 𝔭 ∧ f * (b : F) = (a : F) := by
  classical
  obtain ⟨U, hU, hxU⟩ : ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := by
    obtain ⟨i, y, hy⟩ := X.affineCover.exists_eq x
    exact ⟨(X.affineCover.f i).opensRange, isAffineOpen_opensRange _, hy ▸ ⟨y, rfl⟩⟩
  obtain ⟨xU, rfl⟩ : ∃ xU : ↥U, (xU : X) = x := ⟨⟨x, hxU⟩, rfl⟩
  haveI hlocx : IsLocalization.AtPrime (X.presheaf.stalk (xU : X)) (hU.primeIdealOf xU).asIdeal :=
    hU.isLocalization_stalk xU
  haveI hne : Nonempty U := ⟨xU⟩
  let toF : X.functionField →+* F := (φ.symm : X.functionField ≃+* F).toRingHom
  let rR : Γ(X, U) →+* F := toF.comp (X.germToFunctionField U).hom
  have hrR : ∀ (zU : ↥U) (r : Γ(X, U)), ex X φ (zU : X) (algebraMap Γ(X, U) (X.presheaf.stalk (zU : X)) r) = rR r := by
    intro zU r
    show toF (algebraMap (X.presheaf.stalk (zU : X)) X.functionField
      ((X.presheaf.germ U zU zU.2).hom r)) = toF ((X.germToFunctionField U).hom r)
    congr 1
    rw [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  have hfrac : ∀ (zU : ↥U) (f : F),
      f ∈ SemistableModel.localRing X φ (zU : X) ↔
        ∃ g s : Γ(X, U), s ∉ (hU.primeIdealOf zU).asIdeal ∧ f * rR s = rR g := by
    intro zU f
    haveI hlocz : IsLocalization.AtPrime (X.presheaf.stalk (zU : X)) (hU.primeIdealOf zU).asIdeal :=
      hU.isLocalization_stalk zU
    rw [mem_localRing_iff]
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (hU.primeIdealOf zU).asIdeal.primeCompl g
      refine ⟨r, s, s.2, ?_⟩
      rw [← hrR zU, ← hrR zU, ← map_mul, IsLocalization.mk'_spec]
    · rintro ⟨g, s, hs, hf⟩
      refine ⟨IsLocalization.mk' _ g (⟨s, hs⟩ : (hU.primeIdealOf zU).asIdeal.primeCompl), ?_⟩
      have hs0 : rR s ≠ 0 := by
        rw [← hrR zU]
        exact fun h0 => hs (by
          have := (ex_injective X φ _).eq_iff.mp (h0.trans (map_zero _).symm)
          exact ((IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk (zU : X))
            (hU.primeIdealOf zU).asIdeal s).mp (by rw [this]; exact Ideal.zero_mem _)))
      apply mul_right_cancel₀ hs0
      rw [hf, ← hrR zU, ← map_mul, IsLocalization.mk'_spec, hrR]
  let rRS : Γ(X, U) →+* ↥(SemistableModel.localRing X φ (xU : X)) :=
    (ψ X φ (xU : X)).comp (algebraMap Γ(X, U) (X.presheaf.stalk (xU : X)))
  have hrRS : ∀ r, ((rRS r : ↥(SemistableModel.localRing X φ (xU : X))) : F) = rR r := fun r => by
    show ex X φ (xU : X) _ = rR r; exact hrR xU r
  have hunitS : ∀ s : Γ(X, U), s ∉ (hU.primeIdealOf xU).asIdeal → IsUnit (rRS s) := fun s hs =>
    (IsLocalization.map_units (X.presheaf.stalk (xU : X)) (⟨s, hs⟩ : (hU.primeIdealOf xU).asIdeal.primeCompl)).map
      (ψ X φ (xU : X))
  set 𝔮 : Ideal Γ(X, U) := 𝔭.comap rRS with h𝔮def
  have h𝔭P : 𝔭.IsPrime := inferInstance
  haveI h𝔮p : 𝔮.IsPrime := Ideal.comap_isPrime rRS 𝔭
  have h𝔮le : 𝔮 ≤ (hU.primeIdealOf xU).asIdeal := by
    intro r hr
    by_contra hrx
    exact (Ideal.IsPrime.ne_top h𝔭P) (Ideal.eq_top_of_isUnit_mem _ hr (hunitS r hrx))
  let yU : ↥U := hU.isoSpec.inv.base ⟨𝔮, h𝔮p⟩
  have hyq : hU.primeIdealOf yU = ⟨𝔮, h𝔮p⟩ := by
    show (hU.isoSpec.inv ≫ hU.isoSpec.hom).base ⟨𝔮, h𝔮p⟩ = _
    rw [Iso.inv_hom_id]; rfl
  refine ⟨(yU : X), ?_, fun f => ?_⟩
  ·
    have h1 : (⟨𝔮, h𝔮p⟩ : PrimeSpectrum Γ(X, U)) ⤳ hU.primeIdealOf xU :=
      (PrimeSpectrum.le_iff_specializes _ _).mp h𝔮le
    have h2 : yU ⤳ hU.isoSpec.inv.base (hU.primeIdealOf xU) := h1.map hU.isoSpec.inv.base.hom.continuous
    have h3 : hU.isoSpec.inv.base (hU.primeIdealOf xU) = xU := by
      show (hU.isoSpec.hom ≫ hU.isoSpec.inv).base xU = xU
      rw [Iso.hom_inv_id]; rfl
    rw [h3] at h2
    exact h2.map continuous_subtype_val
  · rw [hfrac yU f, hyq]
    constructor
    · rintro ⟨g, s, hs, hf⟩
      exact ⟨rRS g, rRS s, fun h => hs (show s ∈ 𝔮 from Ideal.mem_comap.mpr h), by rw [hrRS, hrRS]; exact hf⟩
    · rintro ⟨a, b, hb, hf⟩
      obtain ⟨ga, sa, hsa, ha⟩ := (hfrac xU (a : F)).mp a.2
      obtain ⟨gb, sb, hsb, hbb⟩ := (hfrac xU (b : F)).mp b.2
      have hgb : gb ∉ 𝔮 := by
        intro hgb
        apply hb
        have h1 : rRS gb = b * rRS sb := Subtype.ext (by rw [Subring.coe_mul, hrRS, hrRS]; exact hbb.symm)
        have h2 : rRS gb ∈ 𝔭 := hgb
        rw [h1] at h2
        exact ((h𝔭P.mem_or_mem h2).resolve_right
          (fun h => (Ideal.IsPrime.ne_top h𝔭P) (Ideal.eq_top_of_isUnit_mem _ h (hunitS sb hsb))))
      refine ⟨ga * sb, gb * sa, fun hmem' => ?_, ?_⟩
      · rcases (h𝔮p.mem_or_mem hmem') with h | h
        · exact hgb h
        · exact hsa (h𝔮le h)
      · rw [map_mul, map_mul]
        calc f * (rR gb * rR sa) = (f * (b : F) * rR sb) * rR sa := by rw [← hbb]; ring
          _ = (a : F) * rR sa * rR sb := by rw [hf]; ring
          _ = rR ga * rR sb := by rw [ha]

theorem isLocalRing_localRing (z : X) : IsLocalRing ↥(SemistableModel.localRing X φ z) :=
  IsLocalRing.of_surjective' (ψ X φ z) (ψ_bijective X φ z).2

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem specializes_iff_localRing_le {O : Type} [CommRing O] (f : X ⟶ Spec (CommRingCat.of O)) [IsSeparated f]
    (x y : X) : x ⤳ y ↔ SemistableModel.localRing X φ y ≤ SemistableModel.localRing X φ x := by
  classical
  constructor
  ·
    intro h g hg
    obtain ⟨s, rfl⟩ := (mem_localRing_iff X φ y g).mp hg
    refine (mem_localRing_iff X φ x _).mpr ⟨(X.presheaf.stalkSpecializes h).hom s, ?_⟩
    show φ.symm (algebraMap (X.presheaf.stalk x) X.functionField ((X.presheaf.stalkSpecializes h).hom s)) =
      φ.symm (algebraMap (X.presheaf.stalk y) X.functionField s)
    congr 1
    show (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom ((X.presheaf.stalkSpecializes h).hom s) =
      (X.presheaf.stalkSpecializes (genericPoint_specializes y)).hom s
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
  ·
    intro hle
    haveI : ∀ z : X, IsLocalRing ↥(SemistableModel.localRing X φ z) := isLocalRing_localRing X φ
    let R : LocalSubring F := LocalSubring.mk (SemistableModel.localRing X φ x)
    obtain ⟨W, hW⟩ := R.exists_le_valuationSubring
    obtain ⟨hRW, hlocRW⟩ := LocalSubring.le_def.mp hW
    have hyW : SemistableModel.localRing X φ y ≤ W.toSubring := hle.trans hRW
    let ι : ↥(SemistableModel.localRing X φ y) →+* ↥W := Subring.inclusion hyW
    set 𝔮 : Ideal ↥(SemistableModel.localRing X φ y) := (maximalIdeal ↥W).comap ι with h𝔮
    haveI : 𝔮.IsPrime := Ideal.comap_isPrime ι _
    obtain ⟨y', hy'y, hy'⟩ := exists_specializes_localRing_iff X φ y 𝔮
    suffices y' = x by rw [← this]; exact hy'y
    let V : ValuationSubring X.functionField := W.comap (φ.symm : X.functionField ≃+* F).toRingHom
    have hV : ∀ t : X.functionField, t ∈ V ↔ φ.symm t ∈ W := fun t => Iff.rfl
    have hVnu : ∀ t : X.functionField, t ∈ V.nonunits ↔ φ.symm t ∈ W.nonunits := by
      intro t
      rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
        map_eq_zero_iff (φ.symm : X.functionField ≃+* F) φ.symm.injective]
      apply or_congr Iff.rfl
      rw [not_congr (hV t⁻¹), map_inv₀]

    have hunitW : ∀ b : ↥(SemistableModel.localRing X φ y), b ∉ 𝔮 → (b : F) ≠ 0 ∧ (b : F)⁻¹ ∈ W := by
      intro b hb
      have hbu : IsUnit (ι b) := by
        by_contra hnu; exact hb ((mem_maximalIdeal _).mpr hnu)
      obtain ⟨v, hv⟩ := hbu.exists_right_inv
      have hvF : (b : F) * ((v : ↥W) : F) = 1 := by
        have := congrArg (fun t : ↥W => (t : F)) hv
        first | exact this | simpa using this | simpa +zetaDelta using this
      have hb0 : (b : F) ≠ 0 := fun h0 => by rw [h0, zero_mul] at hvF; exact zero_ne_one hvF
      exact ⟨hb0, by rw [inv_eq_of_mul_eq_one_right hvF]; exact v.2⟩

    have h1 : ∀ s : X.presheaf.stalk y', algebraMap (X.presheaf.stalk y') X.functionField s ∈ V := by
      intro s
      rw [hV]
      obtain ⟨a, b, hb, hab⟩ := (hy' _).mp (ex_mem X φ y' s)
      obtain ⟨hb0, hbinv⟩ := hunitW b hb
      have : ex X φ y' s = (a : F) * (b : F)⁻¹ := by rw [← hab, mul_assoc, mul_inv_cancel₀ hb0, mul_one]
      show ex X φ y' s ∈ W
      rw [this]; exact W.mul_mem _ _ (hyW a.2) hbinv
    have h1' : ∀ s ∈ maximalIdeal (X.presheaf.stalk y'),
        algebraMap (X.presheaf.stalk y') X.functionField s ∈ V.nonunits := by
      intro s hs
      obtain ⟨a, b, hb, hab⟩ := (hy' _).mp (ex_mem X φ y' s)
      obtain ⟨hb0, hbinv⟩ := hunitW b hb
      have hsab : ex X φ y' s = (a : F) * (b : F)⁻¹ := by rw [← hab, mul_assoc, mul_inv_cancel₀ hb0, mul_one]
      have ha : a ∈ 𝔮 := by
        by_contra ha
        obtain ⟨ha0, hainv⟩ := hunitW a ha
        apply (mem_maximalIdeal _).mp hs
        have hinv : (b : F) * (a : F)⁻¹ ∈ SemistableModel.localRing X φ y' :=
          (hy' _).mpr ⟨b, a, ha, by rw [mul_assoc, inv_mul_cancel₀ ha0, mul_one]⟩
        obtain ⟨t, ht⟩ := (mem_localRing_iff X φ y' _).mp hinv
        refine IsUnit.of_mul_eq_one (b := t) (ex_injective X φ y' ?_)
        rw [map_mul, map_one, ht, hsab]
        field_simp
      rw [hVnu]
      show ex X φ y' s ∈ W.nonunits
      rw [hsab, ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
      refine ⟨W.mul_mem _ _ (hyW a.2) hbinv, ?_⟩
      have : (⟨(a : F) * (b : F)⁻¹, W.mul_mem _ _ (hyW a.2) hbinv⟩ : ↥W) = ι a * ⟨(b : F)⁻¹, hbinv⟩ := rfl
      rw [this]
      exact Ideal.mul_mem_right _ _ ha

    have h2 : ∀ s : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField s ∈ V := fun s =>
      (hV _).mpr (hRW (ex_mem X φ x s))
    have h2' : ∀ s ∈ maximalIdeal (X.presheaf.stalk x),
        algebraMap (X.presheaf.stalk x) X.functionField s ∈ V.nonunits := by
      intro s hs
      rw [hVnu]
      show ex X φ x s ∈ W.nonunits
      have hnu : ψ X φ x s ∈ maximalIdeal _ := by
        rw [mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        apply (mem_maximalIdeal _).mp hs
        exact (isUnit_map_iff (RingEquiv.ofBijective (ψ X φ x) (ψ_bijective X φ x)) s).mp hu
      rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
      refine ⟨hRW (ex_mem X φ x s), ?_⟩
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hu2 : IsUnit (Subring.inclusion hRW (ψ X φ x s)) := hu
      exact ((mem_maximalIdeal _).mp hnu) (hlocRW.map_nonunit _ hu2)
    exact AlgebraicGeometry.Scheme.eq_of_forall_mem_valuationSubring_of_isSeparated f V y' x h1 h1' h2 h2'

end L1BSpec

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem solution
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (hn₀ : ∀ y : X₀, IsIntegrallyClosed (X₀.presheaf.stalk y))
    {F₀ : Type} [Field F₀] [Algebra A₀ F₀]
    (φ₀ : F₀ ≃+* X₀.functionField)
    (hφ₀ : ∀ a : A₀, φ₀ (algebraMap A₀ F₀ a) = SemistableModel.baseToFunctionField toBase₀ a)

    (hdim : ∀ η y : X₀, toBase₀.base η = closedPoint A₀ → (∃ z : X₀, η ⤳ z ∧ z ≠ η) → η ⤳ y → y ≠ η →
      ∀ z : X₀, y ⤳ z → z = y)

    (hval : ∀ η : X₀, toBase₀.base η = closedPoint A₀ → (∃ y : X₀, η ⤳ y ∧ y ≠ η) →
      ∃ V : ValuationSubring F₀, V.toSubring = SemistableModel.localRing X₀ φ₀ η)

    (hgenX : ∀ V : ValuationSubring F₀, V ≠ ⊤ → (∀ a : A₀, a ≠ 0 → (algebraMap A₀ F₀ a)⁻¹ ∈ V) →
      ∃ y : X₀, V.toSubring = SemistableModel.localRing X₀ φ₀ y)

    (B : Subalgebra A₀ F₀) (hBfg : B.FG) (hBn : ∀ x : F₀, _root_.IsIntegral ↥B x → x ∈ B)
    (hBfrac : ∀ x : F₀, ∃ b c : F₀, b ∈ B ∧ c ∈ B ∧ c ≠ 0 ∧ x * c = b)

    (hdimB : ∀ 𝔮 : Ideal ↥B, 𝔮.IsPrime → Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔮 → ¬ 𝔮.IsMaximal →
      𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes)

    (hgenB : ∀ 𝔭 : Ideal ↥B, 𝔭.IsPrime → 𝔭 ≠ ⊥ → ¬ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔭) →
      ∃ V : ValuationSubring F₀, ∀ f : F₀, f ∈ V ↔ ∃ b c : ↥B, c ∉ 𝔭 ∧ f * (c : F₀) = (b : F₀))

    (hcomp : ∀ η : X₀, toBase₀.base η = closedPoint A₀ → (∃ y : X₀, η ⤳ y ∧ y ≠ η) →
      (B : Set F₀) ⊆ SemistableModel.localRing X₀ φ₀ η →
        ∃ 𝔮 : Ideal ↥B, 𝔮.IsPrime ∧ ∀ x : F₀, x ∈ SemistableModel.localRing X₀ φ₀ η ↔
          ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : F₀) = (b : F₀))
    (hcomp' : ∀ 𝔮 : Ideal ↥B, 𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes →
      ∃ η : X₀, toBase₀.base η = closedPoint A₀ ∧ (∃ y : X₀, η ⤳ y ∧ y ≠ η) ∧
        ∀ x : F₀, x ∈ SemistableModel.localRing X₀ φ₀ η ↔ ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : F₀) = (b : F₀)) :
    ∀ (𝔭 : Ideal ↥B) [𝔭.IsPrime],
      ∃ x : X₀, (∀ f : F₀, f ∈ SemistableModel.localRing X₀ φ₀ x ↔ ∃ b c : ↥B, c ∉ 𝔭 ∧ f * (c : F₀) = (b : F₀)) ∧
        (∀ x' : X₀, (∀ f : F₀, f ∈ SemistableModel.localRing X₀ φ₀ x' ↔ ∃ b c : ↥B, c ∉ 𝔭 ∧ f * (c : F₀) = (b : F₀)) → x' = x) ∧
        (x ∈ toBase₀.smoothLocus ↔ (algebraMap A₀ (Localization.AtPrime 𝔭)).FormallySmooth) := by
  intro 𝔭 _
  classical

  have hex : ∃ x : X₀, ∀ f : F₀, f ∈ SemistableModel.localRing X₀ φ₀ x ↔
      ∃ b c : ↥B, c ∉ 𝔭 ∧ f * (c : F₀) = (b : F₀) := by
    by_cases hsp : Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔭
    · exact AlgebraicGeometry.exists_localRing_eq_localization_of_normal_affineModel_of_map_maximalIdeal_le
        A₀ X₀ toBase₀ hn₀ φ₀ hφ₀ hdim hval B hBfg hBn hBfrac hdimB hcomp hcomp' 𝔭 hsp
    · by_cases h0 : 𝔭 = ⊥
      ·
        refine ⟨genericPoint X₀, fun f => ?_⟩
        constructor
        · intro _
          obtain ⟨b, c, hb, hc, hc0, hf⟩ := hBfrac f
          refine ⟨⟨b, hb⟩, ⟨c, hc⟩, ?_, hf⟩
          rw [h0, Ideal.mem_bot]
          exact fun h => hc0 (congrArg Subtype.val h)
        · intro _
          refine (L1BSpec.mem_localRing_iff X₀ φ₀ (genericPoint X₀) f).mpr ⟨φ₀ f, ?_⟩
          unfold L1BSpec.ex
          rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
          erw [TopCat.Presheaf.stalkSpecializes_refl]
          exact φ₀.symm_apply_apply f
      ·
        obtain ⟨V, hV⟩ := hgenB 𝔭 ‹_› h0 hsp
        have hinj : Function.Injective (fun b : ↥B => (b : F₀)) := Subtype.val_injective
        have hVtop : V ≠ ⊤ := by
          obtain ⟨c, hc𝔭, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
          intro htop
          have hmem : ((c : F₀))⁻¹ ∈ V := by rw [htop]; trivial
          obtain ⟨b, c', hc', h⟩ := (hV _).mp hmem
          apply hc'
          have hcF : (c : F₀) ≠ 0 := fun h0' => hc0 (Subtype.ext h0')
          have : c' = c * b := by
            apply Subtype.ext
            show (c' : F₀) = (c : F₀) * (b : F₀)
            rw [← h, ← mul_assoc, mul_inv_cancel₀ hcF, one_mul]
          rw [this]; exact Ideal.mul_mem_right _ _ hc𝔭
        have hK : ∀ a : A₀, a ≠ 0 → (algebraMap A₀ F₀ a)⁻¹ ∈ V := by
          intro a ha0

          have ha𝔭 : algebraMap A₀ ↥B a ∉ 𝔭 := by
            intro ha
            apply hsp
            have hP : (𝔭.comap (algebraMap A₀ ↥B)).IsPrime := Ideal.comap_isPrime _ _
            have hne : 𝔭.comap (algebraMap A₀ ↥B) ≠ ⊥ := fun hb => ha0 (by
              have : a ∈ 𝔭.comap (algebraMap A₀ ↥B) := ha
              rw [hb] at this; exact this)
            have hmax : (𝔭.comap (algebraMap A₀ ↥B)).IsMaximal := IsPrime.to_maximal_ideal hne
            rw [Ideal.map_le_iff_le_comap, ← IsLocalRing.eq_maximalIdeal hmax]
          have haF : algebraMap A₀ F₀ a ≠ 0 := by
            intro h
            apply ha𝔭
            have : algebraMap A₀ ↥B a = 0 := Subtype.ext (by rw [Subalgebra.coe_algebraMap]; exact h)
            rw [this]; exact 𝔭.zero_mem
          refine (hV _).mpr ⟨1, algebraMap A₀ ↥B a, ha𝔭, ?_⟩
          rw [Subalgebra.coe_algebraMap, inv_mul_cancel₀ haF]; simp
        obtain ⟨y, hy⟩ := hgenX V hVtop hK
        refine ⟨y, fun f => ?_⟩
        rw [← hV f]
        show f ∈ SemistableModel.localRing X₀ φ₀ y ↔ f ∈ V.toSubring
        rw [hy]
  obtain ⟨x, hx⟩ := hex
  refine ⟨x, hx, ?_, ?_⟩
  · intro x' hx'
    exact L1BLO.eq_of_localRing_eq toBase₀ φ₀ x x' (Subring.ext fun f => (hx' f).trans (hx f).symm)
  · exact L1BLO.mem_smoothLocus_iff_of_localRing_eq toBase₀ φ₀ hφ₀ B 𝔭 x hx

end S_AlgebraicGeometry_existsUnique_localRing_eq_localization_of_normal_affineModel_of_relDimOne_of_val_of_gen
end P2MW
export P2MW.S_AlgebraicGeometry_existsUnique_localRing_eq_localization_of_normal_affineModel_of_relDimOne_of_val_of_gen (solution)
