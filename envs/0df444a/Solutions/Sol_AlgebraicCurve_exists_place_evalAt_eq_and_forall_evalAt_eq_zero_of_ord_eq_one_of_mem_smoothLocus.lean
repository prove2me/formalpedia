-- Prove2me | solution 1 for AlgebraicCurve.exists_place_evalAt_eq_and_forall_evalAt_eq_zero_of_ord_eq_one_of_mem_smoothLocus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c92b1cca-4e16-56f8-89cf-64e60a39b101

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_AlgebraicCurve_exists_place_evalAt_eq_of_section_of_ker_eq_span
import Theorems.Thm_AlgebraicCurve_exists_section_localRing_apply_eq_of_ord_eq_one_of_mem_smoothLocus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_place_evalAt_eq_and_forall_evalAt_eq_zero_of_ord_eq_one_of_mem_smoothLocus

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve

namespace M3aGlue

theorem eq_bot_or_eq_maximalIdeal {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (𝔭 : Ideal ↥A) [𝔭.IsPrime] : 𝔭 = ⊥ ∨ 𝔭 = maximalIdeal ↥A := by
  classical
  by_cases h : 𝔭 = ⊥
  · exact Or.inl h
  · right
    obtain ⟨b, hb𝔭, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) ?_
    intro a ha
    obtain ⟨n, c, hc⟩ := hrk a b ha hb0
    have : a ^ n ∈ 𝔭 := by rw [hc]; exact Ideal.mul_mem_right _ _ hb𝔭
    exact Ideal.IsPrime.mem_of_pow_mem ‹_› n this

theorem eq_top_or_eq_of_le {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (W : ValuationSubring L) (hW : A ≤ W) : W = ⊤ ∨ W = A := by
  classical
  by_cases h : W = A
  · exact Or.inr h
  · left
    have hnle : ¬ (W ≤ A) := fun hle => h (le_antisymm hle hW)
    obtain ⟨w, hwW, hwA⟩ := Set.not_subset.mp hnle
    have hw0 : w ≠ 0 := fun h0 => hwA (h0 ▸ A.zero_mem)
    have hwinv : w⁻¹ ∈ A := (A.mem_or_inv_mem w).resolve_left hwA

    have hwinv𝔪 : (⟨w⁻¹, hwinv⟩ : ↥A) ∈ maximalIdeal ↥A := by
      rw [ValuationSubring.valuation_lt_one_iff]
      have h1 : ¬ A.valuation w ≤ 1 := fun hle => hwA ((A.valuation_le_one_iff w).mp hle)
      show A.valuation w⁻¹ < 1
      rw [map_inv₀, inv_lt_one₀ (lt_of_le_of_ne zero_le' ((map_ne_zero A.valuation).mpr hw0).symm)]
      exact lt_of_not_ge h1

    refine eq_top_iff.mpr fun l _ => ?_
    by_cases hlA : l ∈ A
    · exact hW hlA
    · have hl0 : l ≠ 0 := fun h0 => hlA (h0 ▸ A.zero_mem)
      have hlinv : l⁻¹ ∈ A := (A.mem_or_inv_mem l).resolve_left hlA
      have hlinv0 : (⟨l⁻¹, hlinv⟩ : ↥A) ≠ 0 := fun h0 => by
        apply inv_ne_zero hl0; exact congrArg Subtype.val h0
      obtain ⟨n, c, hc⟩ := hrk ⟨w⁻¹, hwinv⟩ ⟨l⁻¹, hlinv⟩ hwinv𝔪 hlinv0

      have hcL : (w⁻¹) ^ n = l⁻¹ * (c : L) := by
        have := congrArg (fun z : ↥A => (z : L)) hc
        simpa using this
      have hl : l = (c : L) * w ^ n := by
        have hwn : w ^ n ≠ 0 := pow_ne_zero _ hw0
        have h1 : l * (w⁻¹) ^ n = (c : L) := by rw [hcL, ← mul_assoc, mul_inv_cancel₀ hl0, one_mul]
        calc l = l * (w⁻¹) ^ n * w ^ n := by rw [inv_pow, mul_assoc, inv_mul_cancel₀ hwn, mul_one]
          _ = (c : L) * w ^ n := by rw [h1]
      rw [hl]
      exact mul_mem (hW c.2) (pow_mem hwW n)

theorem algebraMap_germ_appTop {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of R)) (y : X) (a : R) :
    algebraMap (X.presheaf.stalk y) X.functionField
      ((X.presheaf.germ ⊤ y trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a))) =
    SemistableModel.baseToFunctionField f a := by
  unfold SemistableModel.baseToFunctionField
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply,
    TopCat.Presheaf.germ_stalkSpecializes]

theorem isUnit_germ_appTop_iff {R : Type} [CommRing R] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of R)) (y : X) (a : R) :
    IsUnit ((X.presheaf.germ ⊤ y trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a))) ↔
      a ∉ (f.base y).asIdeal := by

  have h1 : (X.presheaf.germ ⊤ y trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) =
      (f.stalkMap y).hom (((Spec (CommRingCat.of R)).presheaf.germ ⊤ (f.base y) trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) := by
    have h := Scheme.Hom.germ_stalkMap f ⊤ y trivial
    have h' := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) h
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h'
    exact h'.symm
  have h2 : ((Spec (CommRingCat.of R)).presheaf.germ ⊤ (f.base y) trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) = (StructureSheaf.toStalk R (f.base y)).hom a := by
    have h := congrArg (fun g => g.hom a) (StructureSheaf.algebraMap_germ (R := R) ⊤ (f.base y) trivial)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
    rw [Scheme.ΓSpecIso_inv]
    exact h
  rw [h1, h2]

  have hloc : IsLocalHom (f.stalkMap y).hom :=
    Scheme.Hom.instIsLocalHomCarrierStalkCommRingCatPresheafCoeContinuousMapCarrierCarrierHomTopCatBaseRingHomHomStalkMap f y
  have h3 : IsUnit ((f.stalkMap y).hom ((StructureSheaf.toStalk R (f.base y)).hom a)) ↔
      IsUnit ((StructureSheaf.toStalk R (f.base y)).hom a) :=
    ⟨fun hu => hloc.map_nonunit _ hu, fun hu => hu.map _⟩
  rw [h3, ← StructureSheaf.stalkAlgebra_map]

  have h4 : algebraMap R ((Spec.structureSheaf R).presheaf.stalk (f.base y)) a =
      StructureSheaf.stalkIso R (f.base y) (algebraMap R (Localization.AtPrime (f.base y).asIdeal) a) :=
    ((StructureSheaf.stalkIso R (f.base y)).commutes a).symm
  rw [h4]
  have h5 : IsUnit (StructureSheaf.stalkIso R (f.base y) (algebraMap R (Localization.AtPrime (f.base y).asIdeal) a)) ↔
      IsUnit (algebraMap R (Localization.AtPrime (f.base y).asIdeal) a) :=
    ⟨fun hu => by simpa using hu.map (StructureSheaf.stalkIso R (f.base y)).symm, fun hu => hu.map _⟩
  rw [h5, IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime (f.base y).asIdeal) (f.base y).asIdeal]
  rfl

theorem isNoetherianRing_stalk_of_asIdeal_eq_bot {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A)) [LocallyOfFiniteType toBase]
    (y : X) (hy : (toBase.base y).asIdeal = ⊥) :
    IsNoetherianRing (X.presheaf.stalk y) := by
  classical

  obtain ⟨l, hlA⟩ : ∃ l : L, l ∉ A := by
    by_contra h; push Not at h
    exact hA (Set.eq_univ_of_forall fun l => h l)
  have hl0 : l ≠ 0 := fun h0 => hlA (h0 ▸ A.zero_mem)
  have hlinv : l⁻¹ ∈ A := (A.mem_or_inv_mem l).resolve_left hlA
  set a : ↥A := ⟨l⁻¹, hlinv⟩ with hadef
  have ha0 : a ≠ 0 := fun h0 => inv_ne_zero hl0 (congrArg Subtype.val h0)
  have ha𝔪 : a ∈ maximalIdeal ↥A := by
    rw [ValuationSubring.valuation_lt_one_iff]
    have h1 : ¬ A.valuation l ≤ 1 := fun hle => hlA ((A.valuation_le_one_iff l).mp hle)
    show A.valuation l⁻¹ < 1
    rw [map_inv₀, inv_lt_one₀ (lt_of_le_of_ne zero_le' ((map_ne_zero A.valuation).mpr hl0).symm)]
    exact lt_of_not_ge h1

  set a' : Γ(Spec (CommRingCat.of ↥A), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a with ha'
  set U : (Spec (CommRingCat.of ↥A)).Opens := (Spec (CommRingCat.of ↥A)).basicOpen a' with hU
  have hUaff : IsAffineOpen U := (isAffineOpen_top (Spec (CommRingCat.of ↥A))).basicOpen a'
  have hyU : toBase.base y ∈ U := by
    rw [hU, ha', basicOpen_eq_of_affine]
    show a ∉ (toBase.base y).asIdeal
    rw [hy]; exact ha0

  haveI hloc : IsLocalization.Away a' ↑Γ(Spec (CommRingCat.of ↥A), U) := (isAffineOpen_top (Spec (CommRingCat.of ↥A))).isLocalization_basicOpen a'

  let e : ↥A ≃+* ↑Γ(Spec (CommRingCat.of ↥A), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of ↥A)).symm.commRingCatIsoToRingEquiv
  have he : ∀ b : ↥A, e b = (Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv b := fun b => rfl
  have hfield : IsField ↑Γ(Spec (CommRingCat.of ↥A), U) := by
    refine ⟨⟨0, 1, ?_⟩, mul_comm, fun {z} hz => ?_⟩
    · intro h01

      have : (algebraMap ↑Γ(Spec (CommRingCat.of ↥A), ⊤) ↑Γ(Spec (CommRingCat.of ↥A), U)) (e a) ≠ 0 := by
        intro h0
        rw [IsLocalization.map_eq_zero_iff (Submonoid.powers a')] at h0
        obtain ⟨⟨m, hm⟩, hm0⟩ := h0
        obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hm
        have : e (a ^ k * a) = 0 := by rw [map_mul, map_pow, he a]; exact hm0
        exact (mul_ne_zero (pow_ne_zero _ ha0) ha0) (e.injective (by rw [this, map_zero]))
      exact this (by rw [← mul_one ((algebraMap _ _) (e a)), ← h01, mul_zero])
    ·
      obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers a') z
      obtain ⟨x₀, rfl⟩ : ∃ x₀ : ↥A, e x₀ = x := ⟨e.symm x, e.apply_symm_apply x⟩
      have hx₀ : x₀ ≠ 0 := by
        intro h0; apply hz
        show IsLocalization.mk' _ (e x₀) s = 0
        rw [h0, map_zero, IsLocalization.mk'_zero]
      have hunit : IsUnit (algebraMap ↑Γ(Spec (CommRingCat.of ↥A), ⊤) ↑Γ(Spec (CommRingCat.of ↥A), U) (e x₀)) := by
        by_cases hu : IsUnit x₀
        · exact (hu.map e).map _
        · obtain ⟨n, c, hc⟩ := hrk a x₀ ha𝔪 hx₀

          have hau : IsUnit (algebraMap ↑Γ(Spec (CommRingCat.of ↥A), ⊤) ↑Γ(Spec (CommRingCat.of ↥A), U) (e a)) := by
            rw [he]; exact IsLocalization.Away.algebraMap_isUnit a'
          have : IsUnit (algebraMap ↑Γ(Spec (CommRingCat.of ↥A), ⊤) ↑Γ(Spec (CommRingCat.of ↥A), U) (e x₀) *
              algebraMap ↑Γ(Spec (CommRingCat.of ↥A), ⊤) ↑Γ(Spec (CommRingCat.of ↥A), U) (e c)) := by
            rw [← map_mul, ← map_mul, ← hc, map_pow, map_pow]; exact hau.pow n
          exact isUnit_of_mul_isUnit_left this
      obtain ⟨w, hw⟩ := hunit.exists_right_inv
      refine ⟨w * algebraMap _ _ (s : ↑Γ(Spec (CommRingCat.of ↥A), ⊤)), ?_⟩
      show IsLocalization.mk' _ (e x₀) s * (w * _) = 1
      rw [mul_comm w, ← mul_assoc, IsLocalization.mk'_spec, hw]
  letI : Field ↑Γ(Spec (CommRingCat.of ↥A), U) := hfield.toField
  haveI : IsNoetherianRing ↑Γ(Spec (CommRingCat.of ↥A), U) := inferInstance
  haveI : IsLocallyNoetherian (Spec Γ(Spec (CommRingCat.of ↥A), U)) := inferInstance
  haveI : IsLocallyNoetherian ↑U := isLocallyNoetherian_of_isOpenImmersion hUaff.isoSpec.hom

  set V : X.Opens := toBase ⁻¹ᵁ U with hV
  haveI : IsLocallyNoetherian ↑V := LocallyOfFiniteType.isLocallyNoetherian (toBase ∣_ U)
  have hyV : y ∈ V := hyU
  haveI : IsNoetherianRing (((↑V : Scheme).presheaf).stalk (⟨y, hyV⟩ : ↑V)) := inferInstance

  haveI : IsIso (V.ι.stalkMap ⟨y, hyV⟩) := inferInstance
  let ε := (asIso (V.ι.stalkMap ⟨y, hyV⟩)).commRingCatIsoToRingEquiv
  exact isNoetherianRing_of_ringEquiv _ ε.symm

theorem isLocalRing_localRing {F : Type} [Field F] (X : Scheme.{0}) [IsIntegral X]
    (φ : F ≃+* X.functionField) (x : X) : IsLocalRing ↥(SemistableModel.localRing X φ x) := by
  let ex : X.presheaf.stalk x →+* F :=
    (φ.symm : X.functionField ≃+* F).toRingHom.comp (algebraMap (X.presheaf.stalk x) X.functionField)
  have hmem : ∀ g, ex g ∈ SemistableModel.localRing X φ x := fun g => ⟨g, rfl⟩
  let ψ : X.presheaf.stalk x →+* ↥(SemistableModel.localRing X φ x) := ex.codRestrict _ hmem
  have hψ : Function.Surjective ψ := by
    rintro ⟨f, g, rfl⟩
    exact ⟨g, rfl⟩
  exact IsLocalRing.of_surjective' ψ hψ

theorem exists_frac_localRing {F : Type} [Field F] (X : Scheme.{0}) [IsIntegral X]
    (φ : F ≃+* X.functionField) (x : X) :
    ∀ f : F, ∃ a b : ↥(SemistableModel.localRing X φ x), (b : F) ≠ 0 ∧ f * (b : F) = (a : F) := by
  intro f
  let ex : X.presheaf.stalk x →+* F :=
    (φ.symm : X.functionField ≃+* F).toRingHom.comp (algebraMap (X.presheaf.stalk x) X.functionField)
  have hmem : ∀ g, ex g ∈ SemistableModel.localRing X φ x := fun g => ⟨g, rfl⟩
  have hex_inj : Function.Injective ex :=
    φ.symm.injective.comp (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)
  obtain ⟨⟨g, s⟩, hgs⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (X.presheaf.stalk x)) (φ f)
  refine ⟨⟨ex g, hmem g⟩, ⟨ex s, hmem s⟩, ?_, ?_⟩
  · intro h0
    have h0' : ex (s : X.presheaf.stalk x) = 0 := h0
    have : (s : X.presheaf.stalk x) = 0 := hex_inj (by rw [h0', map_zero])
    exact nonZeroDivisors.ne_zero s.2 this
  · show f * ex s = ex g
    apply φ.injective
    have hφex : ∀ t, φ (ex t) = algebraMap (X.presheaf.stalk x) X.functionField t := fun t =>
      φ.apply_symm_apply _
    rw [map_mul, hφex, hφex, ← hgs, IsLocalization.mk'_spec]

end M3aGlue

namespace L1BSec

set_option maxHeartbeats 6400000 in
theorem isNoetherianRing_of_localization_localRing
    {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    {F : Type} [Field F] [Algebra L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A)) [IsIntegral X] [LocallyOfFiniteType toBase]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (x : X) (𝔭 : Ideal ↥(SemistableModel.localRing X φ x)) [𝔭.IsPrime]
    (h𝔭 : ∀ (a : ↥A) (ha : algebraMap L F (a : L) ∈ SemistableModel.localRing X φ x),
      (⟨_, ha⟩ : ↥(SemistableModel.localRing X φ x)) ∈ 𝔭 → a = 0) :
    ∀ O : Subring F, (∀ f : F, f ∈ O ↔ ∃ a b : ↥(SemistableModel.localRing X φ x),
      b ∉ 𝔭 ∧ f * (b : F) = (a : F)) → IsNoetherianRing ↥O := by
  classical
  intro O hO

  let toF : X.functionField →+* F := (φ.symm : X.functionField ≃+* F).toRingHom
  let ex : ∀ z : X, X.presheaf.stalk z →+* F := fun z => toF.comp (algebraMap (X.presheaf.stalk z) X.functionField)
  have hex_inj : ∀ z : X, Function.Injective (ex z) := fun z =>
    φ.symm.injective.comp (IsFractionRing.injective (X.presheaf.stalk z) X.functionField)
  have hmem : ∀ (z : X) (f : F), f ∈ SemistableModel.localRing X φ z ↔ ∃ g, ex z g = f := fun z f => by
    show f ∈ RingHom.range _ ↔ _; rw [RingHom.mem_range]

  obtain ⟨U, hU, hxU⟩ : ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := by
    obtain ⟨i, y, hy⟩ := X.affineCover.exists_eq x
    exact ⟨(X.affineCover.f i).opensRange, isAffineOpen_opensRange _, hy ▸ ⟨y, rfl⟩⟩
  obtain ⟨xU, rfl⟩ : ∃ xU : ↥U, (xU : X) = x := ⟨⟨x, hxU⟩, rfl⟩
  haveI hlocx : IsLocalization.AtPrime (X.presheaf.stalk (xU : X)) (hU.primeIdealOf xU).asIdeal :=
    hU.isLocalization_stalk xU

  haveI hne : Nonempty U := ⟨xU⟩
  let rR : Γ(X, U) →+* F := toF.comp (X.germToFunctionField U).hom
  have hrR : ∀ (zU : ↥U) (r : Γ(X, U)), ex (zU : X) (algebraMap Γ(X, U) (X.presheaf.stalk (zU : X)) r) = rR r := by
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
    rw [hmem]
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
          have := (hex_inj _).eq_iff.mp (h0.trans (map_zero _).symm)
          exact ((IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk (zU : X))
            (hU.primeIdealOf zU).asIdeal s).mp (by rw [this]; exact Ideal.zero_mem _)))
      apply mul_right_cancel₀ hs0
      rw [hf, ← hrR zU, ← map_mul, IsLocalization.mk'_spec, hrR]

  have hψmem : ∀ (z : X) (g : X.presheaf.stalk z), ex z g ∈ SemistableModel.localRing X φ z :=
    fun z g => (hmem z _).mpr ⟨g, rfl⟩
  let ψ : ∀ z : X, X.presheaf.stalk z →+* ↥(SemistableModel.localRing X φ z) := fun z => (ex z).codRestrict _ (hψmem z)
  have hψval : ∀ (z : X) (g : X.presheaf.stalk z), ((ψ z g : ↥(SemistableModel.localRing X φ z)) : F) = ex z g :=
    fun z g => rfl
  have hψbij : ∀ z : X, Function.Bijective (ψ z) := by
    intro z
    refine ⟨fun a b h => hex_inj z (by rw [← hψval, ← hψval, h]), fun s => ?_⟩
    obtain ⟨g, hg⟩ := (hmem z _).mp s.2
    exact ⟨g, Subtype.ext hg⟩

  let rRS : Γ(X, U) →+* ↥(SemistableModel.localRing X φ (xU : X)) :=
    (ψ (xU : X)).comp (algebraMap Γ(X, U) (X.presheaf.stalk (xU : X)))
  have hrRS : ∀ r, ((rRS r : ↥(SemistableModel.localRing X φ (xU : X))) : F) = rR r := fun r => by
    show ex (xU : X) _ = rR r; exact hrR xU r
  have hunitS : ∀ s : Γ(X, U), s ∉ (hU.primeIdealOf xU).asIdeal → IsUnit (rRS s) := fun s hs =>
    (IsLocalization.map_units (X.presheaf.stalk (xU : X)) (⟨s, hs⟩ : (hU.primeIdealOf xU).asIdeal.primeCompl)).map
      (ψ (xU : X))
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

  have hOy : ∀ f : F, f ∈ O ↔ f ∈ SemistableModel.localRing X φ (yU : X) := by
    intro f
    rw [hO f, hfrac yU f, hyq]
    constructor
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
    · rintro ⟨g, s, hs, hf⟩
      exact ⟨rRS g, rRS s, fun h => hs (show s ∈ 𝔮 from Ideal.mem_comap.mpr h), by rw [hrRS, hrRS]; exact hf⟩
  have hOeq : O = SemistableModel.localRing X φ (yU : X) := Subring.ext hOy

  have hconst : ∀ (z : X) (a : ↥A),
      ex z ((X.presheaf.germ ⊤ z trivial).hom (toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))) =
        algebraMap L F (a : L) := by
    intro z a
    show toF (algebraMap (X.presheaf.stalk z) X.functionField _) = _
    rw [M3aGlue.algebraMap_germ_appTop toBase z a, ← hφ]
    exact φ.symm_apply_apply _
  have hy : (toBase.base (yU : X)).asIdeal = ⊥ := by
    refine eq_bot_iff.mpr fun a ha => ?_
    by_contra ha0
    apply (M3aGlue.isUnit_germ_appTop_iff toBase (yU : X) a).not.mpr (not_not.mpr ha)

    set cst : X.presheaf.stalk (yU : X) :=
      (X.presheaf.germ ⊤ (yU : X) trivial).hom (toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a)) with hcst
    have hκS : algebraMap L F (a : L) ∈ SemistableModel.localRing X φ (xU : X) := by
      rw [← hconst (xU : X) a]; exact hψmem _ _
    have hκ𝔭 : (⟨algebraMap L F (a : L), hκS⟩ : ↥(SemistableModel.localRing X φ (xU : X))) ∉ 𝔭 :=
      fun h => ha0 (h𝔭 a hκS h)
    have hκ0 : algebraMap L F (a : L) ≠ 0 := fun h => ha0 (by
      have : ((a : ↥A) : L) = 0 := (map_eq_zero_iff _ (algebraMap L F).injective).mp h
      exact Subtype.ext this)
    have hinvO : (algebraMap L F (a : L))⁻¹ ∈ O :=
      (hO _).mpr ⟨1, ⟨_, hκS⟩, hκ𝔭, by rw [OneMemClass.coe_one]; exact inv_mul_cancel₀ hκ0⟩
    rw [hOy] at hinvO
    obtain ⟨d, hd⟩ := (hmem _ _).mp hinvO
    refine IsUnit.of_mul_eq_one (b := d) (hex_inj _ ?_)
    rw [map_mul, map_one, hd, hcst, hconst, mul_inv_cancel₀ hκ0]

  haveI : IsNoetherianRing (X.presheaf.stalk (yU : X)) :=
    M3aGlue.isNoetherianRing_stalk_of_asIdeal_eq_bot A hrk hA X toBase (yU : X) hy
  rw [hOeq]
  exact isNoetherianRing_of_ringEquiv _ (RingEquiv.ofBijective (ψ (yU : X)) (hψbij _))

end L1BSec

set_option maxHeartbeats 3200000 in
theorem solution
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    [HenselianLocalRing ↥A]
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (x : X) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x) (hxs : x ∈ toBase.smoothLocus)
    (η : X) (hηx : η ⤳ x) (hne : η ≠ x) (hη : toBase.base η = closedPoint ↥A)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar)
    (hR : R.integers.toSubring = SemistableModel.localRing X φ η) :
    let S : Subring F := SemistableModel.localRing X φ x
    (∀ a : ↥A, algebraMap L F (a : L) ∈ S) →
    ∀ (Q : Place (ResidueField ↥A) Fbar), Q.IsRational →
      (∀ f : ↥S, ∃ hR : (f : F) ∈ R.integers, R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring) →
      (∀ (f : ↥S) (hR : (f : F) ∈ R.integers),
        IsUnit f ↔ Q.ord (R.residue ⟨(f : F), hR⟩) = 0 ∧ R.residue ⟨(f : F), hR⟩ ≠ 0) →
      ∀ (T : ↥S), (∃ hR : (T : F) ∈ R.integers, Q.ord (R.residue ⟨(T : F), hR⟩) = 1) →
      ∀ c : ↥A, c ∈ maximalIdeal ↥A →
        (T : F) ≠ algebraMap L F (c : L) ∧
        ∃ P : Place L F,
          (∀ g : F, g ∈ S → g ∈ P.toValuationSubring ∧ ∃ h : P.evalAt g ∈ A,
            (IsUnit (⟨P.evalAt g, h⟩ : ↥A) ↔ ∃ g' ∈ S, g * g' = 1)) ∧
          P.evalAt (T : F) = (c : L) ∧
          (∀ s : F, s ∈ S → P.evalAt s = 0 →
            ∃ s' : F, s' ∈ S ∧ s = ((T : F) - algebraMap L F (c : L)) * s') := by
  intro S hAS Q hQ hread hunits T hordT c hc

  have hTc : (T : F) ≠ algebraMap L F (c : L) := by
    intro h
    obtain ⟨hR, hord⟩ := hordT
    have hcA : algebraMap L F (c : L) ∈ R.integers := (R.algebraMap_mem_iff _).mpr c.2
    have e : (⟨(T : F), hR⟩ : ↥R.integers) = ⟨algebraMap L F (c : L), hcA⟩ := Subtype.ext h
    have h0 : R.residue ⟨(T : F), hR⟩ = 0 := by
      rw [e, R.residue_algebraMap, (IsLocalRing.residue_eq_zero_iff _).mpr hc, map_zero]
    rw [h0, Place.ord_zero] at hord
    exact zero_ne_one hord
  refine ⟨hTc, ?_⟩

  obtain ⟨χ, hχa, hχT, hker⟩ :=
    AlgebraicCurve.exists_section_localRing_apply_eq_of_ord_eq_one_of_mem_smoothLocus A hrk hA X toBase φ hφ x hx hxc hxs
      η hηx hne hη R hR hAS Q hQ hread hunits T hordT c hc

  haveI : IsLocalRing ↥S := M3aGlue.isLocalRing_localRing X φ x
  have hfrac : ∀ f : F, ∃ a b : ↥S, (b : F) ≠ 0 ∧ f * (b : F) = (a : F) := M3aGlue.exists_frac_localRing X φ x
  haveI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
  have hnoeth : ∀ O : Subring F, (∀ f : F, f ∈ O ↔ ∃ a b : ↥S, b ∉ RingHom.ker χ ∧ f * (b : F) = (a : F)) →
      IsNoetherianRing ↥O :=
    L1BSec.isNoetherianRing_of_localization_localRing A hrk hA X toBase φ hφ x (RingHom.ker χ)
      (fun a ha h => by
        have : χ ⟨algebraMap L F (a : L), ha⟩ = 0 := (RingHom.mem_ker).mp h
        rw [show (⟨algebraMap L F (a : L), ha⟩ : ↥S) = ⟨algebraMap L F (a : L), hAS a⟩ from rfl, hχa] at this
        exact this)

  obtain ⟨P, -, -, h1, h2, h3⟩ := AlgebraicCurve.exists_place_evalAt_eq_of_section_of_ker_eq_span A S hAS hfrac T c hTc χ hχa hχT hker hnoeth
  exact ⟨P, h1, h2, h3⟩

end S_AlgebraicCurve_exists_place_evalAt_eq_and_forall_evalAt_eq_zero_of_ord_eq_one_of_mem_smoothLocus
end P2MW
export P2MW.S_AlgebraicCurve_exists_place_evalAt_eq_and_forall_evalAt_eq_zero_of_ord_eq_one_of_mem_smoothLocus (solution)
