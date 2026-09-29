-- Prove2me | solution 1 for AlgebraicGeometry.specializes_iff_localRing_le_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e028a4e7-c310-5b6d-9f66-b9b600cf1850

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicGeometry_Scheme_eq_of_forall_mem_valuationSubring_of_isSeparated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_specializes_iff_localRing_le_of_isSeparated

set_option autoImplicit false

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
        have := congrArg (fun t : ↥W => (t : F)) hv; (simp at this; exact this)
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

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem solution
    (A₀ : Type) [CommRing A₀]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of A₀)) [IsIntegral X] [IsSeparated toBase]
    {F : Type} [Field F] (φ : F ≃+* X.functionField) (x y : X) :
    x ⤳ y ↔ SemistableModel.localRing X φ y ≤ SemistableModel.localRing X φ x :=
  L1BSpec.specializes_iff_localRing_le X φ toBase x y

end S_AlgebraicGeometry_specializes_iff_localRing_le_of_isSeparated
end P2MW
export P2MW.S_AlgebraicGeometry_specializes_iff_localRing_le_of_isSeparated (solution)
