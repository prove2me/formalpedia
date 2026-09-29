-- Prove2me | solution 1 for AlgebraicGeometry.exists_valuationSubring_eq_range_stalk_of_iso_pullback_of_mem_smoothLocus_of_isDiscreteValuationRing_of_specializes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6e5116a8-011b-5032-acd1-d26240de35b5

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicGeometry_isProper_and_flat_and_locallyOfFinitePresentation_of_iso_pullback_specMap
import Theorems.Thm_AlgebraicGeometry_base_genericPoint_eq_and_bijOn_specialFibre_of_iso_pullback_of_residue_surjective_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicCurve_exists_level_mem_functionField_of_iso_pullback_of_isAlgebraic_min2
import Theorems.Thm_AlgebraicGeometry_isDiscreteValuationRing_stalk_of_mem_smoothLocus_of_forall_specializes_eq
import Theorems.Thm_AlgebraicGeometry_isDiscreteValuationRing_stalk_of_isPullback_of_isDiscreteValuationRing_stalk
import Theorems.Thm_IsLocalRing_mem_range_algebraMap_of_flat_of_isLocalHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_valuationSubring_eq_range_stalk_of_iso_pullback_of_mem_smoothLocus_of_isDiscreteValuationRing_of_specializes
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

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

end M3aGlue

section MainE

open M3aGlue

theorem solution
    {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (hres : Function.Surjective ((IsLocalRing.residue ↥A).comp ι))
    (halg : ∀ a : ↥A, IsAlgebraic ↥(ι.range) a)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (hn₀ : ∀ y : X₀, IsIntegrallyClosed (X₀.presheaf.stalk y))

    (hO : Function.Bijective (fun a : A₀ => toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))

    (hgen₀ : ∀ y : X₀, (toBase₀.base y).asIdeal = ⊥ → y ∈ toBase₀.smoothLocus)

    (hsm₀ : ∀ η₀ : X₀, toBase₀.base η₀ = closedPoint A₀ → (∃ y : X₀, η₀ ⤳ y ∧ y ≠ η₀) → η₀ ∈ toBase₀.smoothLocus)

    (hdim₀ : ∀ η y : X₀, toBase₀.base η = closedPoint A₀ → (∃ z : X₀, η ⤳ z ∧ z ≠ η) → η ⤳ y → y ≠ η →
      ∀ z : X₀, y ⤳ z → z = y)
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase)
    [hX : IsIntegral X] :
    let pr := iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))
    ∀ η : X, toBase.base η = closedPoint ↥A → (∃ y : X, η ⤳ y ∧ y ≠ η) →
      ∃ O : ValuationSubring X.functionField,
        O.toSubring = (algebraMap (X.presheaf.stalk η) X.functionField).range ∧
        ∀ (hgen : pr.base (genericPoint X) = genericPoint X₀) (g : X₀.functionField),
          (pr.stalkMap (genericPoint X)).hom
              ((X₀.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom g) ∈ O ↔
            g ∈ (algebraMap (X₀.presheaf.stalk (pr.base η)) X₀.functionField).range := by
  intro pr η hη hηnc
  classical
  obtain ⟨instP, instF, instL⟩ := AlgebraicGeometry.isProper_and_flat_and_locallyOfFinitePresentation_of_iso_pullback_specMap A hrk hA A₀ ι hι hres halg X₀ toBase₀ hn₀ hO hgen₀ hsm₀ X toBase iso hiso
  obtain ⟨hgenpt, hspecial, hinj, hsurj, hspec⟩ := AlgebraicGeometry.base_genericPoint_eq_and_bijOn_specialFibre_of_iso_pullback_of_residue_surjective_of_isDiscreteValuationRing A hrk hA A₀ ι hι hres halg X₀ toBase₀ hn₀ hO hgen₀ hsm₀ X toBase iso hiso

  have hη₀sp : toBase₀.base ((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base η) = closedPoint A₀ := (hspecial η).1 hη

  have hη₀nc : ∃ y₀ : X₀, (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base η ⤳ y₀ ∧ y₀ ≠ (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base η := by
    obtain ⟨y, hy, hyne⟩ := hηnc
    have hysp : toBase.base y = closedPoint ↥A := by
      have h1 : toBase.base η ⤳ toBase.base y := hy.map toBase.base.hom.continuous
      rw [hη] at h1
      apply PrimeSpectrum.ext
      exact le_antisymm (IsLocalRing.le_maximalIdeal (toBase.base y).isPrime.ne_top)
        ((PrimeSpectrum.le_iff_specializes _ _).2 h1)
    exact ⟨(iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base y, (hspec η y hη hysp).1 hy, fun h => hyne (hinj y η hysp hη h)⟩

  have hη₀gen : ∀ ζ₀ : X₀, ζ₀ ⤳ (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base η → toBase₀.base ζ₀ = closedPoint A₀ → ζ₀ = (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base η := by
    intro ζ₀ hζ₀ hζ₀sp
    by_contra hne
    obtain ⟨y₀, hy₀, hy₀ne⟩ := hη₀nc
    have := hdim₀ ζ₀ ((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base η) hζ₀sp ⟨_, hζ₀, fun h => hne h.symm⟩ hζ₀ (fun h => hne h.symm) y₀ hy₀
    exact hy₀ne this

  have hη₀sm : (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base η ∈ toBase₀.smoothLocus := by
    obtain ⟨y, hy, hyne⟩ := hηnc
    have hysp : toBase.base y = closedPoint ↥A := by
      have h1 : toBase.base η ⤳ toBase.base y := hy.map toBase.base.hom.continuous
      rw [hη] at h1
      apply PrimeSpectrum.ext
      exact le_antisymm (IsLocalRing.le_maximalIdeal (toBase.base y).isPrime.ne_top)
        ((PrimeSpectrum.le_iff_specializes _ _).2 h1)
    refine hsm₀ _ hη₀sp ⟨(iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base y, (hspec η y hη hysp).1 hy, fun h => hyne (hinj y η hysp hη h)⟩

  obtain ⟨ϖ₀, hϖ₀⟩ := (IsPrincipalIdealRing.principal (maximalIdeal A₀)).principal
  obtain ⟨hDVR₀, h𝔪₀⟩ :=
    AlgebraicGeometry.isDiscreteValuationRing_stalk_of_mem_smoothLocus_of_forall_specializes_eq
      A₀ ϖ₀ hϖ₀ X₀ toBase₀ ((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base η) hη₀sp hη₀sm hη₀gen

  have hflat_of_inj : ∀ {B : Type} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] (j : B →+* ↥A),
      Function.Injective j → j.Flat := by
    intro B _ _ _ j hj
    letI : Algebra B ↥A := j.toAlgebra
    haveI : Module.IsTorsionFree B ↥A := by
      refine ⟨fun r hr a b hab => ?_⟩
      have hr0 : r ≠ 0 := by rintro rfl; exact not_isRegular_zero hr
      have : j r * a = j r * b := hab
      exact mul_left_cancel₀ (fun h => hr0 (hj (by rw [h, map_zero]))) this
    have hflat : Module.Flat B ↥A := by
      rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
      infer_instance
    exact hflat

  have hXgen : genericPoint X ⤳ η := (genericPoint_spec X).specializes trivial

  have hval : ∀ f : X.functionField,
      f ∈ (algebraMap (X.presheaf.stalk η) X.functionField).range ∨
      f⁻¹ ∈ (algebraMap (X.presheaf.stalk η) X.functionField).range := by
    intro f
    obtain ⟨A₁, _instA₁, _instD₁, _instDVR₁, ι₁', _instL₁', ι₁, _instL₁, hι₁, hcomp, ϖ₁, hϖ₁, X₁, _instI₁, f₁, g₁, hsq,
        e₁, he₁, he₁', hgen1, u, hu⟩ :=
      AlgebraicCurve.exists_level_mem_functionField_of_iso_pullback_of_isAlgebraic_min2 A hrk X toBase A₀ ι hι ϖ₀ hϖ₀ halg X₀ toBase₀ iso hiso ![f]

    have hg₁ : g₁.base ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base η) = (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base η := by
      have h := congrArg (fun k : X ⟶ X₀ => k.base η) he₁'
      simpa only [Scheme.Hom.comp_base, TopCat.comp_app] using h
    have hη₁ : f₁.base ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base η) = closedPoint A₁ := by
      have h1 : ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))) ≫ f₁).base η = (toBase ≫ Spec.map (CommRingCat.ofHom ι₁)).base η := by
        rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, he₁]
      change f₁.base ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base η) = _
      rw [← Scheme.Hom.comp_apply, h1, Scheme.Hom.comp_apply, hη]
      exact Spec_closedPoint (f := CommRingCat.ofHom ι₁)
    have hι₁'inj : Function.Injective ι₁' := by
      intro a b h
      apply hι
      rw [← hcomp, RingHom.comp_apply, RingHom.comp_apply, h]
    have hres₁ : Function.Surjective ((IsLocalRing.residue A₁).comp ι₁') := by
      intro k
      obtain ⟨a₁, rfl⟩ := IsLocalRing.residue_surjective k
      obtain ⟨a₀, ha₀⟩ := hres (IsLocalRing.residue ↥A (ι₁ a₁))
      refine ⟨a₀, ?_⟩
      change IsLocalRing.residue A₁ (ι₁' a₀) = IsLocalRing.residue A₁ a₁
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      change IsLocalRing.residue ↥A (ι a₀) = IsLocalRing.residue ↥A (ι₁ a₁) at ha₀
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← hcomp, RingHom.comp_apply, ← map_sub] at ha₀
      exact (IsLocalRing.mem_maximalIdeal _).2 (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha₀ (hu.map ι₁))

    obtain ⟨hDVR0', h𝔪0'⟩ := AlgebraicGeometry.isDiscreteValuationRing_stalk_of_mem_smoothLocus_of_forall_specializes_eq A₀ ϖ₀ hϖ₀ X₀ toBase₀ (g₁.base ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base η))
      (by rw [hg₁]; exact hη₀sp) (by rw [hg₁]; exact hη₀sm) (by rw [hg₁]; exact hη₀gen)
    haveI := hDVR0'
    obtain ⟨instDom1, hDVR1, -⟩ := AlgebraicGeometry.isDiscreteValuationRing_stalk_of_isPullback_of_isDiscreteValuationRing_stalk A₀ ϖ₀ hϖ₀ A₁ ι₁' hι₁'inj hres₁ ϖ₁ hϖ₁ X₀ toBase₀ X₁ f₁ g₁ hsq
      ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base η) hη₁ h𝔪0'
    haveI := hDVR1

    let θ : X₁.functionField →+* X.functionField :=
      ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap (genericPoint X)).hom.comp (X₁.presheaf.stalkSpecializes (specializes_of_eq hgen1)).hom
    have hcomm : ∀ r : X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base η),
        θ (algebraMap _ X₁.functionField r) =
        algebraMap (X.presheaf.stalk η) X.functionField (((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap η).hom r) := by
      intro r
      change ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap (genericPoint X)).hom ((X₁.presheaf.stalkSpecializes (specializes_of_eq hgen1)).hom
        ((X₁.presheaf.stalkSpecializes ((genericPoint_spec X₁).specializes (Set.mem_univ _))).hom r)) =
        (X.presheaf.stalkSpecializes hXgen).hom (((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap η).hom r)
      rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply (e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))) (genericPoint X) η hXgen r]
      congr 1
      change (X₁.presheaf.stalkSpecializes ((genericPoint_spec X₁).specializes (Set.mem_univ _)) ≫
        X₁.presheaf.stalkSpecializes (specializes_of_eq hgen1)).hom r = _
      rw [TopCat.Presheaf.stalkSpecializes_comp]
    have hf : f = θ (u 0) := by have h__af := hu 0; simp at h__af; exact h__af
    rcases ValuationRing.isInteger_or_isInteger (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base η)) (u 0) with ⟨r, hr⟩ | ⟨r, hr⟩
    · left
      refine ⟨((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap η).hom r, ?_⟩
      rw [← hcomm, hr, hf]
    · right
      refine ⟨((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap η).hom r, ?_⟩
      rw [← hcomm, hr, hf, map_inv₀]
  let O : ValuationSubring X.functionField :=
    { (algebraMap (X.presheaf.stalk η) X.functionField).range with mem_or_inv_mem' := hval }
  refine ⟨O, rfl, ?_⟩

  intro hgen0 g
  haveI : Flat pr := by
    haveI : (CommRingCat.ofHom ι).hom.Flat := hflat_of_inj ι hι
    haveI : Flat (Spec.map (CommRingCat.ofHom ι)) := Flat.SpecMap_iff.mpr ‹_›
    change Flat (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    infer_instance
  let θ₀ : X₀.functionField →+* X.functionField :=
    (pr.stalkMap (genericPoint X)).hom.comp (X₀.presheaf.stalkSpecializes (specializes_of_eq hgen0)).hom
  have hcomm0 : ∀ r : X₀.presheaf.stalk (pr.base η),
      θ₀ (algebraMap _ X₀.functionField r) =
      algebraMap (X.presheaf.stalk η) X.functionField ((pr.stalkMap η).hom r) := by
    intro r
    change (pr.stalkMap (genericPoint X)).hom ((X₀.presheaf.stalkSpecializes (specializes_of_eq hgen0)).hom
      ((X₀.presheaf.stalkSpecializes ((genericPoint_spec X₀).specializes (Set.mem_univ _))).hom r)) =
      (X.presheaf.stalkSpecializes hXgen).hom ((pr.stalkMap η).hom r)
    rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply pr (genericPoint X) η hXgen r]
    congr 1
    change (X₀.presheaf.stalkSpecializes ((genericPoint_spec X₀).specializes (Set.mem_univ _)) ≫
      X₀.presheaf.stalkSpecializes (specializes_of_eq hgen0)).hom r = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]
  change θ₀ g ∈ O ↔ _
  constructor
  · intro hg
    letI algK : Algebra X₀.functionField X.functionField := θ₀.toAlgebra
    letI algN : Algebra (X₀.presheaf.stalk (pr.base η)) X.functionField :=
      (θ₀.comp (algebraMap _ X₀.functionField)).toAlgebra
    haveI : IsScalarTower (X₀.presheaf.stalk (pr.base η)) X₀.functionField X.functionField :=
      IsScalarTower.of_algebraMap_eq (fun r => rfl)
    exact IsLocalRing.mem_range_algebraMap_of_flat_of_isLocalHom (pr.stalkMap η).hom
      (AlgebraicGeometry.Flat.stalkMap pr η) X₀.functionField X.functionField hcomm0 g hg
  · rintro ⟨r, rfl⟩
    change θ₀ (algebraMap _ _ r) ∈ (algebraMap (X.presheaf.stalk η) X.functionField).range
    rw [hcomm0]
    exact ⟨_, rfl⟩

end MainE

end S_AlgebraicGeometry_exists_valuationSubring_eq_range_stalk_of_iso_pullback_of_mem_smoothLocus_of_isDiscreteValuationRing_of_specializes
end P2MW
export P2MW.S_AlgebraicGeometry_exists_valuationSubring_eq_range_stalk_of_iso_pullback_of_mem_smoothLocus_of_isDiscreteValuationRing_of_specializes (solution)
