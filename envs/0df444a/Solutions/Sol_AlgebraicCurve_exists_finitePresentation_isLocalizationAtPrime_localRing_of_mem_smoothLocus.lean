-- Prove2me | solution 1 for AlgebraicCurve.exists_finitePresentation_isLocalizationAtPrime_localRing_of_mem_smoothLocus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/dc86a7c6-3a0a-5c0d-b105-f1cbba02347a

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_SemistableModel_isPrincipalIdealRing_stalk_quotient_map_maximalIdeal_of_mem_smoothLocus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_finitePresentation_isLocalizationAtPrime_localRing_of_mem_smoothLocus

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

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
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_finitePresentation_isLocalizationAtPrime_localRing_of_mem_smoothLocus.M3aGlue"

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
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_finitePresentation_isLocalizationAtPrime_localRing_of_mem_smoothLocus.M3aGlue"

namespace M3aGlue

section FiniteQuot

open IsLocalRing

theorem moduleFinite_quotient_span_of_residue_surjective
    {A Q : Type} [CommRing A] [CommRing Q] [IsDomain Q] [IsPrincipalIdealRing Q] [IsLocalRing Q] [Algebra A Q]
    (hnf : ¬ IsField Q) (hres : ∀ q : Q, ∃ a : A, q - algebraMap A Q a ∈ maximalIdeal Q)
    (q : Q) (hq : q ≠ 0) :
    Module.Finite A (Q ⧸ Ideal.span {q}) := by
  classical
  haveI : IsDiscreteValuationRing Q :=
    { not_a_field' := by rwa [ne_eq, ← IsLocalRing.isField_iff_maximalIdeal_eq] }
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible Q
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hq hπ
  have hspan : Ideal.span {q} = Ideal.span {π ^ n} := Ideal.span_singleton_eq_span_singleton.2 hn
  rw [hspan]
  clear hspan hn hq q
  have hπm : maximalIdeal Q = Ideal.span {π} := hπ.maximalIdeal_eq
  induction n with
  | zero =>
    have : Subsingleton (Q ⧸ Ideal.span {(π ^ 0 : Q)}) := by
      rw [pow_zero, Ideal.span_singleton_one]
      exact Ideal.Quotient.subsingleton_iff.2 rfl
    infer_instance
  | succ n ih =>
    have hle : Ideal.span {π ^ (n + 1)} ≤ Ideal.span {π ^ n} := by
      rw [Ideal.span_singleton_le_span_singleton]
      exact ⟨π, by ring⟩
    let f : (Q ⧸ Ideal.span {π ^ (n + 1)}) →ₐ[A] (Q ⧸ Ideal.span {π ^ n}) := Ideal.Quotient.factorₐ A hle
    have hfs : Function.Surjective f := Ideal.Quotient.factor_surjective hle

    have hker : LinearMap.ker f.toLinearMap = Submodule.span A {Ideal.Quotient.mk (Ideal.span {π ^ (n + 1)}) (π ^ n)} := by
      apply le_antisymm
      · intro m hm
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
        rw [LinearMap.mem_ker] at hm
        change Ideal.Quotient.factor hle (Ideal.Quotient.mk _ r) = 0 at hm
        rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hm
        obtain ⟨s, rfl⟩ := hm
        obtain ⟨a, ha⟩ := hres s
        rw [hπm, Ideal.mem_span_singleton] at ha
        obtain ⟨t, ht⟩ := ha
        have : Ideal.Quotient.mk (Ideal.span {π ^ (n + 1)}) (π ^ n * s) =
            a • Ideal.Quotient.mk (Ideal.span {π ^ (n + 1)}) (π ^ n) := by
          rw [Algebra.smul_def, IsScalarTower.algebraMap_apply A Q (Q ⧸ Ideal.span {π ^ (n + 1)}) a,
            Ideal.Quotient.algebraMap_eq, ← map_mul, eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem,
            Ideal.mem_span_singleton]
          refine ⟨-t, ?_⟩
          have : s = algebraMap A Q a + π * t := by rw [← ht]; ring
          rw [this]; ring
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
      · rw [Submodule.span_le]
        rintro _ rfl
        rw [SetLike.mem_coe, LinearMap.mem_ker]
        change Ideal.Quotient.factor hle (Ideal.Quotient.mk _ (π ^ n)) = 0
        rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span rfl
    haveI : Module.Finite A ↥(LinearMap.ker f.toLinearMap) := by
      rw [hker]; exact Module.Finite.span_of_finite A (Set.finite_singleton _)
    haveI : Module.Finite A ((Q ⧸ Ideal.span {π ^ (n + 1)}) ⧸ LinearMap.ker f.toLinearMap) :=
      Module.Finite.equiv (f.toLinearMap.quotKerEquivOfSurjective hfs).symm
    exact Module.Finite.of_submodule_quotient (LinearMap.ker f.toLinearMap)

end FiniteQuot
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_finitePresentation_isLocalizationAtPrime_localRing_of_mem_smoothLocus.M3aGlue"

end M3aGlue
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_finitePresentation_isLocalizationAtPrime_localRing_of_mem_smoothLocus.M3aGlue"

section MainPB

open M3aGlue

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
    ∃ (ι : ↥A →+* ↥S) (_ : ∀ a : ↥A, ((ι a : ↥S) : F) = algebraMap L F (a : L))
      (B : Type) (_ : CommRing B) (_ : Algebra ↥A B) (_ : Algebra B ↥S) (𝔫 : Ideal B) (_ : 𝔫.IsPrime),
      letI : Algebra ↥A ↥S := ι.toAlgebra
      Algebra.FinitePresentation ↥A B ∧ 𝔫.comap (algebraMap ↥A B) = maximalIdeal ↥A ∧
      IsScalarTower ↥A B ↥S ∧ IsLocalization.AtPrime ↥S 𝔫 ∧ Module.Flat ↥A ↥S ∧
      ∀ (h : F) (hh : h ∈ S), h ≠ 0 → h⁻¹ ∈ R.integers →
        Ideal.Quotient.mk ((maximalIdeal ↥A).map (algebraMap ↥A ↥S)) ⟨h, hh⟩ ∈
            nonZeroDivisors (↥S ⧸ (maximalIdeal ↥A).map (algebraMap ↥A ↥S)) ∧
          Module.Finite ↥A (↥S ⧸ (Ideal.span ({⟨h, hh⟩} : Set ↥S) ⊔ (maximalIdeal ↥A).map (algebraMap ↥A ↥S))) := by
  intro S
  classical

  have hφ' : ∀ a : ↥A, φ.symm (SemistableModel.baseToFunctionField toBase a) = algebraMap L F (a : L) := fun a => by
    rw [← hφ, RingEquiv.symm_apply_apply]
  let cstHom : ∀ z : X, ↥A →+* X.presheaf.stalk z := fun z =>
    (X.presheaf.germ ⊤ z trivial).hom.comp (toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom)
  have hcst : ∀ (z : X) (a : ↥A), locHom φ z (cstHom z a) = algebraMap L F (a : L) := fun z a => by
    rw [locHom_apply]
    change φ.symm (algebraMap _ _ ((X.presheaf.germ ⊤ z trivial).hom
      (toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a)))) = _
    rw [algebraMap_germ_appTop toBase z a, hφ']
  have hcstU : ∀ (z : X) (a : ↥A), IsUnit (cstHom z a) ↔ a ∉ (toBase.base z).asIdeal := fun z a => by
    change IsUnit ((X.presheaf.germ ⊤ z trivial).hom
      (toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))) ↔ _
    exact isUnit_germ_appTop_iff toBase z a

  let ι : ↥A →+* ↥S := (locEquiv φ x).toRingHom.comp (cstHom x)
  have hι : ∀ a : ↥A, ((ι a : ↥S) : F) = algebraMap L F (a : L) := fun a => hcst x a

  let U : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.f _)
  have hxU : x ∈ U := X.affineCover.covers x
  have hle : U ≤ toBase ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of ↥A)).Opens) := le_top
  let fAB : ↥A →+* Γ(X, U) := (toBase.appLE ⊤ U hle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom
  letI algAB : Algebra ↥A Γ(X, U) := fAB.toAlgebra
  let gBS : Γ(X, U) →+* ↥S := (locEquiv φ x).toRingHom.comp (X.presheaf.germ U x hxU).hom
  letI algBS : Algebra Γ(X, U) ↥S := gBS.toAlgebra
  let 𝔫 : Ideal Γ(X, U) := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal

  have hgerm : ∀ a : ↥A, (X.presheaf.germ U x hxU).hom (fAB a) = cstHom x a := by
    intro a
    change (X.presheaf.germ U x hxU).hom ((X.presheaf.map (homOfLE hle).op).hom
      (toBase.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))) = _
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]
    rfl

  letI algBst : Algebra Γ(X, U) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have hloc0 : IsLocalization.AtPrime (X.presheaf.stalk x) 𝔫 := hU.isLocalization_stalk ⟨x, hxU⟩
  let e : X.presheaf.stalk x ≃ₐ[Γ(X, U)] ↥S :=
    AlgEquiv.ofRingEquiv (f := locEquiv φ x) (fun b => rfl)
  have hloc : @IsLocalization.AtPrime _ _ ↥S _ algBS 𝔫 (hU.primeIdealOf ⟨x, hxU⟩).isPrime :=
    IsLocalization.isLocalization_of_algEquiv 𝔫.primeCompl e
  letI : Algebra ↥A ↥S := ι.toAlgebra
  have htower : IsScalarTower ↥A Γ(X, U) ↥S := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    change ι a = gBS (fAB a)
    change (locEquiv φ x) (cstHom x a) = (locEquiv φ x) ((X.presheaf.germ U x hxU).hom (fAB a))
    rw [hgerm]
  refine ⟨ι, hι, Γ(X, U), inferInstance, algAB, algBS, 𝔫, (hU.primeIdealOf ⟨x, hxU⟩).isPrime, ?_, ?_, htower, hloc, ?_, ?_⟩
  ·
    have h1 : (toBase.appLE ⊤ U hle).hom.FinitePresentation :=
      HasRingHomProperty.appLE @LocallyOfFinitePresentation toBase inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ hle
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom.FinitePresentation :=
      RingHom.FinitePresentation.of_bijective (Scheme.ΓSpecIso (CommRingCat.of ↥A)).symm.commRingCatIsoToRingEquiv.bijective
    exact h1.comp h2
  ·
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top (Ideal.comap_isPrime _ _))
    · intro a ha
      rw [Ideal.mem_comap]
      change fAB a ∈ 𝔫
      rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x) 𝔫 (fAB a)]
      change (X.presheaf.germ U x hxU).hom (fAB a) ∈ maximalIdeal _
      rw [hgerm]
      intro hu
      exact ((hcstU x a).1 hu) (by rw [hx]; exact ha)
  ·
    haveI : Module.Flat ↥A Γ(X, U) := by
      have h1 : (toBase.appLE ⊤ U hle).hom.Flat :=
        HasRingHomProperty.appLE @Flat toBase inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ hle
      have h2 : (Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom.Flat :=
        RingHom.Flat.of_bijective (Scheme.ΓSpecIso (CommRingCat.of ↥A)).symm.commRingCatIsoToRingEquiv.bijective
      exact h2.comp h1
    haveI : Module.Flat Γ(X, U) ↥S := IsLocalization.flat ↥S 𝔫.primeCompl
    exact Module.Flat.trans ↥A Γ(X, U) ↥S
  ·
    obtain ⟨hD, hPIR, hnf, hrat⟩ :=
      AlgebraicCurve.SemistableModel.isPrincipalIdealRing_stalk_quotient_map_maximalIdeal_of_mem_smoothLocus
        A X toBase φ hφ x hx hxc hxs
    intro h hh h0 hinv

    set J : Ideal ↥S := (maximalIdeal ↥A).map (algebraMap ↥A ↥S) with hJdef
    have hIJ : J = ((maximalIdeal ↥A).map (cstHom x)).map ((locEquiv φ x : X.presheaf.stalk x ≃+* ↥S) : X.presheaf.stalk x →+* ↥S) := by
      rw [hJdef, Ideal.map_map]; rfl
    let qe := Ideal.quotientEquiv _ J (locEquiv φ x) hIJ
    haveI : IsDomain (↥S ⧸ J) := Function.Injective.isDomain qe.symm.toRingHom qe.symm.injective
    haveI : IsPrincipalIdealRing (↥S ⧸ J) := IsPrincipalIdealRing.of_surjective qe.toRingHom qe.surjective
    have hnf' : ¬ IsField (↥S ⧸ J) := fun hf => hnf (MulEquiv.isField hf qe.toMulEquiv)
    haveI : IsLocalRing ↥S := IsLocalRing.of_surjective' (locEquiv φ x).toRingHom (locEquiv φ x).surjective
    haveI : IsLocalRing (↥S ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    haveI : IsLocalHom (Ideal.Quotient.mk J) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hresQ : ∀ q : ↥S ⧸ J, ∃ a : ↥A, q - algebraMap ↥A (↥S ⧸ J) a ∈ maximalIdeal (↥S ⧸ J) := by
      intro q
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
      obtain ⟨b, rfl⟩ := (locEquiv φ x).surjective s
      obtain ⟨a, ha⟩ := hrat b
      refine ⟨a, ?_⟩
      have : algebraMap ↥A (↥S ⧸ J) a = Ideal.Quotient.mk J (locEquiv φ x (cstHom x a)) := rfl
      rw [this, ← map_sub, ← map_sub]
      refine map_nonunit (Ideal.Quotient.mk J) _ ?_
      intro hu
      exact ha (by have h__af := hu.map (locEquiv φ x).symm.toRingHom; simp at h__af; exact h__af)

    have hnotJ : (⟨h, hh⟩ : ↥S) ∉ J := by
      intro hmem
      set s : X.presheaf.stalk x := (locEquiv φ x).symm ⟨h, hh⟩ with hsdef
      have hs : s ∈ (maximalIdeal ↥A).map (cstHom x) := by
        rw [hIJ, Ideal.map_comap_of_equiv, Ideal.mem_comap] at hmem
        exact hmem
      have hsh : locHom φ x s = h := by
        have := congrArg Subtype.val ((locEquiv φ x).apply_symm_apply ⟨h, hh⟩)
        rw [coe_locEquiv] at this
        exact this
      let spec := (X.presheaf.stalkSpecializes hηx).hom
      have hcomp : spec.comp (cstHom x) = cstHom η := by
        ext a
        change (X.presheaf.germ ⊤ x trivial ≫ X.presheaf.stalkSpecializes hηx).hom _ = (X.presheaf.germ ⊤ η trivial).hom _
        rw [TopCat.Presheaf.germ_stalkSpecializes]
      have h1 : spec s ∈ (maximalIdeal ↥A).map (cstHom η) := by
        rw [← hcomp, ← Ideal.map_map]
        exact Ideal.mem_map_of_mem _ hs
      have h2 : (maximalIdeal ↥A).map (cstHom η) ≤ maximalIdeal (X.presheaf.stalk η) := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha hu
        exact (hcstU η a).1 hu (by rw [hη]; exact ha)
      have h3 : IsUnit (spec s) := by
        rw [isUnit_iff_exists_mul_eq_one φ η]
        refine ⟨h⁻¹, ?_, ?_⟩
        · have : h⁻¹ ∈ R.integers.toSubring := hinv
          rwa [hR] at this
        · rw [locHom_stalkSpecializes φ hηx s, hsh, mul_inv_cancel₀ h0]
      exact h2 h1 h3
    have hq0 : Ideal.Quotient.mk J ⟨h, hh⟩ ≠ 0 := fun h0' => hnotJ ((Ideal.Quotient.eq_zero_iff_mem).1 h0')
    refine ⟨mem_nonZeroDivisors_of_ne_zero hq0, ?_⟩
    haveI hfin : Module.Finite ↥A ((↥S ⧸ J) ⧸ Ideal.span {Ideal.Quotient.mk J ⟨h, hh⟩}) :=
      moduleFinite_quotient_span_of_residue_surjective hnf' hresQ _ hq0
    have hspan : (Ideal.span {(⟨h, hh⟩ : ↥S)}).map (Ideal.Quotient.mk J) = Ideal.span {Ideal.Quotient.mk J ⟨h, hh⟩} := by
      rw [Ideal.map_span, Set.image_singleton]
    let e2 := DoubleQuot.quotQuotEquivQuotSupₐ ↥A J (Ideal.span {(⟨h, hh⟩ : ↥S)})
    haveI : Module.Finite ↥A ((↥S ⧸ J) ⧸ (Ideal.span {(⟨h, hh⟩ : ↥S)}).map (Ideal.Quotient.mkₐ ↥A J)) := by
      change Module.Finite ↥A ((↥S ⧸ J) ⧸ (Ideal.span {(⟨h, hh⟩ : ↥S)}).map (Ideal.Quotient.mk J))
      rw [hspan]; exact hfin
    have := Module.Finite.equiv e2.toLinearEquiv
    rw [sup_comm]
    exact this

end MainPB
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_finitePresentation_isLocalizationAtPrime_localRing_of_mem_smoothLocus.M3aGlue"

end S_AlgebraicCurve_exists_finitePresentation_isLocalizationAtPrime_localRing_of_mem_smoothLocus
end P2MW
export P2MW.S_AlgebraicCurve_exists_finitePresentation_isLocalizationAtPrime_localRing_of_mem_smoothLocus (solution)
