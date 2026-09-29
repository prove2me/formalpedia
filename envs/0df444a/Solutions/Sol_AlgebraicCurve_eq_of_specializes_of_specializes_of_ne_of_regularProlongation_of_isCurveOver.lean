-- Prove2me | solution 1 for AlgebraicCurve.eq_of_specializes_of_specializes_of_ne_of_regularProlongation_of_isCurveOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d9add130-0654-5052-b93d-ac3e4b77b6f6

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_eq_of_specializes_of_specializes_of_ne_of_regularProlongation_of_isCurveOver

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

open IntermediateField in
open scoped IntermediateField.algebraAdjoinAdjoin in
theorem M3aGlue.trdeg_eq_one
    (K F : Type*) [Field K] [Field F] [Algebra K F] [PerfectField K]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    Algebra.trdeg K F = 1 := by

  have hex : ∃ x : F, Transcendental K x := by
    by_contra h
    push_neg at h
    haveI : Algebra.IsAlgebraic K F := ⟨fun x => not_not.1 (h x)⟩
    haveI : Algebra.FormallyUnramified K F := Algebra.FormallyUnramified.of_isSeparable K F
    exact false_of_nontrivial_of_subsingleton Ω[F⁄K]
  obtain ⟨x, hx⟩ := hex
  have hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F :=
    AlgebraicCurve.IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType hx
  apply le_antisymm
  ·
    haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F := Algebra.IsAlgebraic.of_finite _ F
    haveI : Algebra.IsAlgebraic (Algebra.adjoin K ({x} : Set F)) F :=
      (IsFractionRing.comap_isAlgebraic_iff (A := Algebra.adjoin K ({x} : Set F))
        (K := IntermediateField.adjoin K ({x} : Set F)) (C := F)).2 inferInstance
    have h := Algebra.IsAlgebraic.trdeg_le_cardinalMk K ({x} : Set F)
    rwa [Cardinal.mk_singleton] at h
  ·
    have hind : AlgebraicIndependent K ![x] := algebraicIndependent_iff_transcendental.2 hx
    have h := hind.lift_cardinalMk_le_trdeg
    rw [Cardinal.mk_fintype, Fintype.card_unique] at h
    simpa using h

namespace M3aGlue

section Transport

variable {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X] (φ : F ≃+* X.functionField)

noncomputable def locHom (z : X) : X.presheaf.stalk z →+* F :=
  (φ.symm : X.functionField ≃+* F).toRingHom.comp (algebraMap (X.presheaf.stalk z) X.functionField)

theorem locHom_apply (z : X) (s : X.presheaf.stalk z) :
    locHom φ z s = φ.symm (algebraMap (X.presheaf.stalk z) X.functionField s) := rfl

theorem φ_locHom (z : X) (s : X.presheaf.stalk z) :
    φ (locHom φ z s) = algebraMap (X.presheaf.stalk z) X.functionField s := by
  rw [locHom_apply, RingEquiv.apply_symm_apply]

theorem locHom_injective (z : X) : Function.Injective (locHom φ z) :=
  φ.symm.injective.comp (IsFractionRing.injective (X.presheaf.stalk z) X.functionField)

theorem range_locHom (z : X) : (locHom φ z).range = SemistableModel.localRing X φ z := rfl

theorem mem_localRing_iff (z : X) (f : F) :
    f ∈ SemistableModel.localRing X φ z ↔ ∃ s, locHom φ z s = f := Iff.rfl

theorem locHom_mem (z : X) (s : X.presheaf.stalk z) : locHom φ z s ∈ SemistableModel.localRing X φ z :=
  ⟨s, rfl⟩

noncomputable def locEquiv (z : X) : X.presheaf.stalk z ≃+* ↥(SemistableModel.localRing X φ z) :=
  RingEquiv.ofBijective (locHom φ z).rangeRestrict
    ⟨fun a b h => locHom_injective φ z (congrArg Subtype.val h), (locHom φ z).rangeRestrict_surjective⟩

@[scoped simp] theorem coe_locEquiv (z : X) (s : X.presheaf.stalk z) :
    ((locEquiv φ z s : ↥(SemistableModel.localRing X φ z)) : F) = locHom φ z s := rfl

theorem isUnit_iff_exists_mul_eq_one (z : X) (s : X.presheaf.stalk z) :
    IsUnit s ↔ ∃ g ∈ SemistableModel.localRing X φ z, locHom φ z s * g = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨locHom φ z ((u⁻¹ : (X.presheaf.stalk z)ˣ) : X.presheaf.stalk z), locHom_mem φ z _, ?_⟩
    rw [← map_mul, Units.mul_inv, map_one]
  · rintro ⟨g, ⟨t, rfl⟩, h⟩
    change locHom φ z s * locHom φ z t = 1 at h
    rw [← map_mul] at h
    have h1 : s * t = 1 := locHom_injective φ z (by rw [h, map_one])
    exact IsUnit.of_mul_eq_one t h1

theorem locHom_stalkSpecializes {z₁ z₂ : X} (h : z₁ ⤳ z₂) (s : X.presheaf.stalk z₂) :
    locHom φ z₁ ((X.presheaf.stalkSpecializes h).hom s) = locHom φ z₂ s := by
  simp only [locHom_apply, RingHom.algebraMap_toAlgebra]
  congr 1
  change (X.presheaf.stalkSpecializes h ≫ X.presheaf.stalkSpecializes _).hom s = _
  rw [TopCat.Presheaf.stalkSpecializes_comp]

theorem localRing_le_of_specializes {z₁ z₂ : X} (h : z₁ ⤳ z₂) :
    SemistableModel.localRing X φ z₂ ≤ SemistableModel.localRing X φ z₁ := by
  rintro f ⟨s, rfl⟩
  exact ⟨(X.presheaf.stalkSpecializes h).hom s, locHom_stalkSpecializes φ h s⟩

noncomputable def VK (V : ValuationSubring F) : ValuationSubring X.functionField :=
  V.comap (φ.symm : X.functionField ≃+* F).toRingHom

theorem mem_VK_iff (V : ValuationSubring F) (k : X.functionField) : k ∈ VK φ V ↔ φ.symm k ∈ V := Iff.rfl

theorem algebraMap_mem_VK_iff (V : ValuationSubring F) (z : X) (s : X.presheaf.stalk z) :
    algebraMap (X.presheaf.stalk z) X.functionField s ∈ VK φ V ↔ locHom φ z s ∈ V := Iff.rfl

theorem mem_VK_nonunits_iff (V : ValuationSubring F) (k : X.functionField) :
    k ∈ (VK φ V).nonunits ↔ φ.symm k ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, mem_VK_iff, map_inv₀,
    map_eq_zero_iff _ φ.symm.injective]

theorem forall_mem_VK_iff (V : ValuationSubring F) (z : X) :
    (∀ s : X.presheaf.stalk z, algebraMap (X.presheaf.stalk z) X.functionField s ∈ VK φ V) ↔
      SemistableModel.localRing X φ z ≤ V.toSubring := by
  constructor
  · rintro h f ⟨s, rfl⟩; exact h s
  · intro h s; exact h (locHom_mem φ z s)

theorem mem_nonunits_iff_not_isUnit (V : ValuationSubring F) {f : F} (hf : f ∈ V) :
    f ∈ V.nonunits ↔ ¬ IsUnit (⟨f, hf⟩ : ↥V) := by
  have := (ValuationSubring.coe_mem_nonunits_iff (A := V) (a := ⟨f, hf⟩))
  exact this

end Transport

end M3aGlue
p2m_reactivate "P2MW.S_AlgebraicCurve_eq_of_specializes_of_specializes_of_ne_of_regularProlongation_of_isCurveOver.M3aGlue"

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
p2m_reactivate "P2MW.S_AlgebraicCurve_eq_of_specializes_of_specializes_of_ne_of_regularProlongation_of_isCurveOver.M3aGlue"

namespace M3aGlue

open MvPolynomial

theorem dimensionLEOne_of_finiteType_of_trdeg_le_one
    (k : Type*) (B : Type*) [Field k] [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    (htr : Algebra.trdeg k B ≤ 1) : Ring.DimensionLEOne B := by
  classical
  obtain ⟨s, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k B

  have hs : s ≤ 1 := by
    have hind : AlgebraicIndependent k (fun i : Fin s => g (X i)) := by
      rw [algebraicIndependent_iff_injective_aeval]
      have : (aeval fun i : Fin s => g (X i) : MvPolynomial (Fin s) k →ₐ[k] B) = g := by
        ext i
        simp
      rw [this]; exact hg
    have h1 := hind.lift_cardinalMk_le_trdeg
    rw [Cardinal.mk_fin, Cardinal.lift_natCast] at h1
    have h2 : Cardinal.lift.{0} (Algebra.trdeg k B) ≤ Cardinal.lift.{0} (1 : Cardinal) := Cardinal.lift_le.2 htr
    rw [Cardinal.lift_one] at h2
    have h3 := h1.trans h2
    norm_cast at h3
  letI : Algebra (MvPolynomial (Fin s) k) B := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) B := ⟨hint⟩
  haveI : Ring.DimensionLEOne (MvPolynomial (Fin s) k) := by
    interval_cases s
    ·
      haveI : IsPrincipalIdealRing (MvPolynomial (Fin 0) k) :=
        IsPrincipalIdealRing.of_surjective (MvPolynomial.isEmptyRingEquiv k (Fin 0)).symm.toRingHom
          (MvPolynomial.isEmptyRingEquiv k (Fin 0)).symm.surjective
      infer_instance
    ·
      let e : MvPolynomial (Fin 1) k ≃ₐ[k] Polynomial k :=
        (MvPolynomial.finSuccEquiv k 0).trans (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv k (Fin 0)))
      haveI : IsPrincipalIdealRing (MvPolynomial (Fin 1) k) :=
        IsPrincipalIdealRing.of_surjective e.symm.toRingEquiv.toRingHom e.symm.surjective
      infer_instance
  exact Ring.DimensionLEOne.of_isIntegral (MvPolynomial (Fin s) k) B

end M3aGlue
p2m_reactivate "P2MW.S_AlgebraicCurve_eq_of_specializes_of_specializes_of_ne_of_regularProlongation_of_isCurveOver.M3aGlue"

namespace M3aGlue

theorem isAlgClosed_residueField {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) :
    IsAlgClosed (ResidueField ↥A) := by
  classical
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hl : p ∈ Polynomial.lifts (IsLocalRing.residue ↥A) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n; exact IsLocalRing.residue_surjective (p.coeff n)
  obtain ⟨q, hqp, hqdeg, hqmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hp
  have hdeg : (q.map (algebraMap ↥A L)).degree ≠ 0 := by
    rw [hqmon.degree_map, hqdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg
  have hxint : IsIntegral ↥A x := ⟨q, hqmon, by rwa [← Polynomial.eval_map]⟩
  obtain ⟨a, rfl⟩ : ∃ a : ↥A, algebraMap ↥A L a = x := IsIntegrallyClosed.algebraMap_eq_of_integral hxint
  refine ⟨IsLocalRing.residue ↥A a, ?_⟩
  have hqa : q.eval a = 0 := by
    apply (IsFractionRing.injective ↥A L)
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
    exact hx
  rw [← hqp, Polynomial.eval_map, Polynomial.eval₂_at_apply, hqa, map_zero]

end M3aGlue
p2m_reactivate "P2MW.S_AlgebraicCurve_eq_of_specializes_of_specializes_of_ne_of_regularProlongation_of_isCurveOver.M3aGlue"

section MainHDIM

open M3aGlue

theorem solution
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    [HenselianLocalRing ↥A]
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y))
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (η : X) (hη : toBase.base η = closedPoint ↥A) (hηnc : ∃ y : X, η ⤳ y ∧ y ≠ η)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    [IsCurveOver (ResidueField ↥A) Fbar] [Algebra.EssFiniteType (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar)
    (hR : R.integers.toSubring = SemistableModel.localRing X φ η)
    (y : X) (hy : η ⤳ y) (hyη : y ≠ η) (y' : X) (hy' : y ⤳ y') :
    y' = y := by
  classical
  have hηy' : η ⤳ y' := hy.trans hy'

  let qη : PrimeSpectrum (X.presheaf.stalk y') :=
    (Spec.map (X.presheaf.stalkSpecializes hηy')).base (closedPoint (X.presheaf.stalk η))
  let qy : PrimeSpectrum (X.presheaf.stalk y') :=
    (Spec.map (X.presheaf.stalkSpecializes hy')).base (closedPoint (X.presheaf.stalk y))
  have hqη : (X.fromSpecStalk y').base qη = η := by
    change (Spec.map (X.presheaf.stalkSpecializes hηy') ≫ X.fromSpecStalk y').base (closedPoint _) = η
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.fromSpecStalk_closedPoint
  have hqy : (X.fromSpecStalk y').base qy = y := by
    change (Spec.map (X.presheaf.stalkSpecializes hy') ≫ X.fromSpecStalk y').base (closedPoint _) = y
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.fromSpecStalk_closedPoint
  have hemb := (X.fromSpecStalk y').isEmbedding
  have hle : qη.asIdeal ≤ qy.asIdeal := by
    have h0 : (X.fromSpecStalk y').base qη ⤳ (X.fromSpecStalk y').base qy := by rw [hqη, hqy]; exact hy
    have h1 : qη ⤳ qy := hemb.isInducing.specializes_iff.1 h0
    exact (PrimeSpectrum.le_iff_specializes qη qy).2 h1
  have hne : qη ≠ qy := by
    intro h
    apply hyη
    rw [← hqη, ← hqy, h]
  have hqηdef : qη.asIdeal = (maximalIdeal (X.presheaf.stalk η)).comap (X.presheaf.stalkSpecializes hηy').hom := rfl
  have hqydef : qy.asIdeal = (maximalIdeal (X.presheaf.stalk y)).comap (X.presheaf.stalkSpecializes hy').hom := rfl

  obtain ⟨_, ⟨U, hU, rfl⟩, hy'U, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y') isOpen_univ
  have hyU : y ∈ U := hy'.mem_open U.2 hy'U
  have hηU : η ∈ U := hηy'.mem_open U.2 hy'U
  have hle' : U ≤ toBase ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of ↥A)).Opens) := le_top

  let fAB : ↥A →+* Γ(X, U) := (toBase.appLE ⊤ U hle').hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom
  let g' : Γ(X, U) →+* X.presheaf.stalk y' := (X.presheaf.germ U y' hy'U).hom
  let gη : Γ(X, U) →+* X.presheaf.stalk η := (X.presheaf.germ U η hηU).hom
  have hgη : ∀ b, gη b = (X.presheaf.stalkSpecializes hηy').hom (g' b) := fun b => by
    change _ = (X.presheaf.germ U y' hy'U ≫ X.presheaf.stalkSpecializes hηy').hom b
    rw [TopCat.Presheaf.germ_stalkSpecializes]

  letI algBO : Algebra Γ(X, U) (X.presheaf.stalk y') := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y', hy'U⟩
  haveI hlocO : IsLocalization.AtPrime (X.presheaf.stalk y') (hU.primeIdealOf ⟨y', hy'U⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y', hy'U⟩

  let 𝔮 : Ideal Γ(X, U) := qη.asIdeal.comap g'
  haveI h𝔮p : 𝔮.IsPrime := Ideal.comap_isPrime g' qη.asIdeal
  have hmem𝔮 : ∀ b, b ∈ 𝔮 ↔ gη b ∈ maximalIdeal (X.presheaf.stalk η) := fun b => by
    change g' b ∈ qη.asIdeal ↔ _
    rw [hqηdef, Ideal.mem_comap, hgη]

  have hφ' : ∀ a : ↥A, φ.symm (SemistableModel.baseToFunctionField toBase a) = algebraMap L F (a : L) := fun a => by
    rw [← hφ, RingEquiv.symm_apply_apply]
  have hgerm : ∀ a : ↥A, gη (fAB a) = (X.presheaf.germ ⊤ η trivial).hom
      (toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a)) := by
    intro a
    change (X.presheaf.germ U η hηU).hom ((X.presheaf.map (homOfLE hle').op).hom
      (toBase.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))) = _
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]
    rfl
  have hcst : ∀ a : ↥A, locHom φ η (gη (fAB a)) = algebraMap L F (a : L) := fun a => by
    rw [hgerm, locHom_apply]
    change φ.symm (algebraMap _ _ ((X.presheaf.germ ⊤ η trivial).hom
      (toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a)))) = _
    rw [algebraMap_germ_appTop toBase η a, hφ']
  have hcstU : ∀ a : ↥A, IsUnit (gη (fAB a)) ↔ a ∉ (toBase.base η).asIdeal := fun a => by
    rw [hgerm]; exact isUnit_germ_appTop_iff toBase η a

  have hRmem : ∀ s : X.presheaf.stalk η, locHom φ η s ∈ R.integers := fun s => by
    have : locHom φ η s ∈ R.integers.toSubring := by rw [hR]; exact locHom_mem φ η s
    exact this
  let toR : X.presheaf.stalk η →+* ↥R.integers := (locHom φ η).codRestrict R.integers.toSubring hRmem
  have htoR_unit : ∀ s, IsUnit s ↔ IsUnit (toR s) := by
    intro s
    rw [isUnit_iff_exists_mul_eq_one φ η s]
    constructor
    · rintro ⟨g, hg, h1⟩
      have hg' : g ∈ R.integers := by rw [show (g ∈ R.integers) = (g ∈ R.integers.toSubring) from rfl, hR]; exact hg
      exact ⟨⟨⟨_, hRmem s⟩, ⟨g, hg'⟩, Subtype.ext h1, Subtype.ext (by rw [mul_comm]; exact h1)⟩, rfl⟩
    · rintro ⟨u, hu⟩
      refine ⟨((u⁻¹ : (↥R.integers)ˣ) : ↥R.integers), ?_, ?_⟩
      · have : (((u⁻¹ : (↥R.integers)ˣ) : ↥R.integers) : F) ∈ R.integers.toSubring := Subtype.mem _
        rwa [hR] at this
      · have := congrArg Subtype.val u.mul_inv
        rw [hu] at this
        exact this
  let ρ : Γ(X, U) →+* Fbar := R.residue.comp (toR.comp gη)
  have hρ : ∀ b, ρ b = R.residue (toR (gη b)) := fun b => rfl
  have hkerρ : ∀ b, ρ b = 0 ↔ b ∈ 𝔮 := by
    intro b
    rw [hmem𝔮, hρ, ← RingHom.mem_ker, R.ker_residue, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, mem_nonunits_iff, htoR_unit]

  haveI : IsAlgClosed (ResidueField ↥A) := isAlgClosed_residueField A
  have h𝔪𝔮 : ∀ a ∈ maximalIdeal ↥A, fAB a ∈ 𝔮 := by
    intro a ha
    rw [hmem𝔮]
    intro hu
    exact (hcstU a).1 hu (by rw [hη]; exact ha)
  let κC : ResidueField ↥A →+* Γ(X, U) ⧸ 𝔮 :=
    Ideal.Quotient.lift (maximalIdeal ↥A) ((Ideal.Quotient.mk 𝔮).comp fAB)
      (fun a ha => (Ideal.Quotient.eq_zero_iff_mem).2 (h𝔪𝔮 a ha))
  letI algκC : Algebra (ResidueField ↥A) (Γ(X, U) ⧸ 𝔮) := κC.toAlgebra

  haveI : Algebra.FiniteType (ResidueField ↥A) (Γ(X, U) ⧸ 𝔮) := by
    have h1 : (toBase.appLE ⊤ U hle').hom.FinitePresentation :=
      HasRingHomProperty.appLE @LocallyOfFinitePresentation toBase inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ hle'
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom.FinitePresentation :=
      RingHom.FinitePresentation.of_bijective (Scheme.ΓSpecIso (CommRingCat.of ↥A)).symm.commRingCatIsoToRingEquiv.bijective
    have h3 : fAB.FiniteType := RingHom.FiniteType.of_finitePresentation (h1.comp h2)
    have h4 : ((Ideal.Quotient.mk 𝔮).comp fAB).FiniteType :=
      (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp h3
    have h5 : (κC.comp (IsLocalRing.residue ↥A)) = (Ideal.Quotient.mk 𝔮).comp fAB := by
      ext a; rfl
    rw [← h5] at h4
    exact RingHom.FiniteType.of_comp_finiteType h4

  let ψ : (Γ(X, U) ⧸ 𝔮) →+* Fbar := Ideal.Quotient.lift 𝔮 ρ (fun b hb => (hkerρ b).2 hb)
  have hψinj : Function.Injective ψ := by
    rw [RingHom.injective_iff_ker_eq_bot, ← le_bot_iff]
    intro c hc
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [RingHom.mem_ker] at hc
    change ρ b = 0 at hc
    exact (Ideal.Quotient.eq_zero_iff_mem).2 ((hkerρ b).1 hc)
  have hψalg : ∀ k : ResidueField ↥A, ψ (algebraMap (ResidueField ↥A) _ k) = algebraMap (ResidueField ↥A) Fbar k := by
    intro k
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective k
    change ρ (fAB a) = algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A a)
    rw [hρ, ← R.residue_algebraMap a]
    congr 1
    apply Subtype.ext
    exact hcst a
  let ψₐ : (Γ(X, U) ⧸ 𝔮) →ₐ[ResidueField ↥A] Fbar :=
    { toRingHom := ψ, commutes' := hψalg }

  have htr : Algebra.trdeg (ResidueField ↥A) (Γ(X, U) ⧸ 𝔮) ≤ 1 := by
    have := trdeg_le_of_injective ψₐ hψinj
    rw [trdeg_eq_one (ResidueField ↥A) Fbar] at this
    exact this
  haveI hdim : Ring.DimensionLEOne (Γ(X, U) ⧸ 𝔮) :=
    dimensionLEOne_of_finiteType_of_trdeg_le_one (ResidueField ↥A) (Γ(X, U) ⧸ 𝔮) htr

  have key : qy.asIdeal = maximalIdeal (X.presheaf.stalk y') := by
    by_contra hqy'
    have hlt2 : qy.asIdeal < maximalIdeal _ :=
      lt_of_le_of_ne (IsLocalRing.le_maximalIdeal qy.isPrime.ne_top) hqy'
    have hlt1 : qη.asIdeal < qy.asIdeal := lt_of_le_of_ne hle (fun h => hne (PrimeSpectrum.ext h))

    have hcomap_inj : ∀ I J : Ideal (X.presheaf.stalk y'), I.comap g' = J.comap g' → I = J := by
      intro I J h
      have hI := IsLocalization.map_under (hU.primeIdealOf ⟨y', hy'U⟩).asIdeal.primeCompl (X.presheaf.stalk y') I
      have hJ := IsLocalization.map_under (hU.primeIdealOf ⟨y', hy'U⟩).asIdeal.primeCompl (X.presheaf.stalk y') J
      change (I.comap g').map g' = I at hI
      change (J.comap g').map g' = J at hJ
      rw [← hI, ← hJ, h]
    have hlt1' : 𝔮 < qy.asIdeal.comap g' :=
      lt_of_le_of_ne (Ideal.comap_mono hle) (fun h => hlt1.ne (hcomap_inj _ _ h))
    have hlt2' : qy.asIdeal.comap g' < (maximalIdeal _).comap g' :=
      lt_of_le_of_ne (Ideal.comap_mono hlt2.le) (fun h => hlt2.ne (hcomap_inj _ _ h))
    haveI : (qy.asIdeal.comap g').IsPrime := Ideal.comap_isPrime g' _
    haveI : ((maximalIdeal (X.presheaf.stalk y')).comap g').IsPrime := Ideal.comap_isPrime g' _

    have hk1 : 𝔮 ≤ qy.asIdeal.comap g' := hlt1'.le
    have hk2 : 𝔮 ≤ (maximalIdeal (X.presheaf.stalk y')).comap g' := hk1.trans hlt2'.le
    have hP1 : (Ideal.map (Ideal.Quotient.mk 𝔮) (qy.asIdeal.comap g')).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    have hP2 : (Ideal.map (Ideal.Quotient.mk 𝔮) ((maximalIdeal (X.presheaf.stalk y')).comap g')).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    have hstrict : ∀ I J : Ideal Γ(X, U), 𝔮 ≤ I → I < J →
        I.map (Ideal.Quotient.mk 𝔮) < J.map (Ideal.Quotient.mk 𝔮) := by
      intro I J hI hIJ
      refine lt_of_le_of_ne (Ideal.map_mono hIJ.le) fun h => hIJ.ne ?_
      have h1 := Ideal.comap_map_of_surjective (Ideal.Quotient.mk 𝔮) Ideal.Quotient.mk_surjective I
      have h2 := Ideal.comap_map_of_surjective (Ideal.Quotient.mk 𝔮) Ideal.Quotient.mk_surjective J
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 hI] at h1
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 (hI.trans hIJ.le)] at h2
      rw [← h1, ← h2, h]
    have hbot : (⊥ : Ideal (Γ(X, U) ⧸ 𝔮)) < (qy.asIdeal.comap g').map (Ideal.Quotient.mk 𝔮) := by
      have := hstrict 𝔮 _ le_rfl hlt1'
      rwa [Ideal.map_quotient_self] at this
    exact Ring.DimensionLEOne.not_lt_lt ⊥ _ _ ⟨hbot, hstrict _ _ hk1 hlt2'⟩
  have hq : qy = closedPoint (X.presheaf.stalk y') := PrimeSpectrum.ext key
  rw [← hqy, hq]
  exact Scheme.fromSpecStalk_closedPoint.symm

end MainHDIM
p2m_reactivate "P2MW.S_AlgebraicCurve_eq_of_specializes_of_specializes_of_ne_of_regularProlongation_of_isCurveOver.M3aGlue"

end S_AlgebraicCurve_eq_of_specializes_of_specializes_of_ne_of_regularProlongation_of_isCurveOver
end P2MW
export P2MW.S_AlgebraicCurve_eq_of_specializes_of_specializes_of_ne_of_regularProlongation_of_isCurveOver (solution)
