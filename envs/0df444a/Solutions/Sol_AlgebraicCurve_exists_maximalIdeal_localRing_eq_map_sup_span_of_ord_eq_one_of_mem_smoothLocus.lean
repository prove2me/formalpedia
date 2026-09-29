-- Prove2me | solution 1 for AlgebraicCurve.exists_maximalIdeal_localRing_eq_map_sup_span_of_ord_eq_one_of_mem_smoothLocus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/5040a483-9a63-505a-bb4c-522841736dfa

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_SemistableModel_isPrincipalIdealRing_stalk_quotient_map_maximalIdeal_of_mem_smoothLocus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_maximalIdeal_localRing_eq_map_sup_span_of_ord_eq_one_of_mem_smoothLocus

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
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_maximalIdeal_localRing_eq_map_sup_span_of_ord_eq_one_of_mem_smoothLocus.M3aGlue"

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
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_maximalIdeal_localRing_eq_map_sup_span_of_ord_eq_one_of_mem_smoothLocus.M3aGlue"

section MainCX

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
    (∀ a : ↥A, algebraMap L F (a : L) ∈ S) →
    ∀ (Q : Place (ResidueField ↥A) Fbar), Q.IsRational →
      (∀ f : ↥S, ∃ hR : (f : F) ∈ R.integers, R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring) →
      (∀ (f : ↥S) (hR : (f : F) ∈ R.integers),
        IsUnit f ↔ Q.ord (R.residue ⟨(f : F), hR⟩) = 0 ∧ R.residue ⟨(f : F), hR⟩ ≠ 0) →
      ∀ (T : ↥S), (∃ hR : (T : F) ∈ R.integers, Q.ord (R.residue ⟨(T : F), hR⟩) = 1) →
      ∃ (ι : ↥A →+* ↥S) (_ : ∀ a : ↥A, ((ι a : ↥S) : F) = algebraMap L F (a : L)) (_ : IsLocalRing ↥S),
        maximalIdeal ↥S = (maximalIdeal ↥A).map ι ⊔ Ideal.span {T} ∧
        T ∉ (maximalIdeal ↥A).map ι ∧
        Function.Surjective ((IsLocalRing.residue ↥S).comp ι) := by
  intro S hconstS Q hQrat hRES hUNITS T hT
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
  let ι : ↥A →+* ↥S := (locEquiv φ x).toRingHom.comp (cstHom x)
  have hι : ∀ a : ↥A, ((ι a : ↥S) : F) = algebraMap L F (a : L) := fun a => hcst x a
  haveI hlocS : IsLocalRing ↥S := IsLocalRing.of_surjective' (locEquiv φ x).toRingHom (locEquiv φ x).surjective

  obtain ⟨hD, hPIR, hnf, hrat⟩ :=
    AlgebraicCurve.SemistableModel.isPrincipalIdealRing_stalk_quotient_map_maximalIdeal_of_mem_smoothLocus
      A X toBase φ hφ x hx hxc hxs
  set J : Ideal ↥S := (maximalIdeal ↥A).map ι with hJdef
  have hIJ : J = ((maximalIdeal ↥A).map (cstHom x)).map ((locEquiv φ x : X.presheaf.stalk x ≃+* ↥S) : X.presheaf.stalk x →+* ↥S) := by
    rw [hJdef, Ideal.map_map]; rfl
  let qe := Ideal.quotientEquiv _ J (locEquiv φ x) hIJ
  haveI : IsDomain (↥S ⧸ J) := Function.Injective.isDomain qe.symm.toRingHom qe.symm.injective
  haveI : IsPrincipalIdealRing (↥S ⧸ J) := IsPrincipalIdealRing.of_surjective qe.toRingHom qe.surjective
  have hnf' : ¬ IsField (↥S ⧸ J) := fun hf => hnf (MulEquiv.isField hf qe.toMulEquiv)
  haveI : IsLocalRing (↥S ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  haveI hmkloc : IsLocalHom (Ideal.Quotient.mk J) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsDiscreteValuationRing (↥S ⧸ J) :=
    { not_a_field' := by rwa [ne_eq, ← IsLocalRing.isField_iff_maximalIdeal_eq] }

  have hSR : ∀ f : ↥S, (f : F) ∈ R.integers := fun f => (hRES f).1
  let ρ : ↥S →+* Fbar := R.residue.comp
    { toFun := fun f => ⟨(f : F), hSR f⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hρ : ∀ f : ↥S, ρ f = R.residue ⟨(f : F), hSR f⟩ := fun f => rfl
  have hρι : ∀ a : ↥A, ρ (ι a) = algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A a) := by
    intro a
    rw [hρ]
    have : (⟨((ι a : ↥S) : F), hSR (ι a)⟩ : ↥R.integers) =
        ⟨algebraMap L F (a : L), (R.algebraMap_mem_iff (a : L)).mpr a.2⟩ := Subtype.ext (hι a)
    rw [this, R.residue_algebraMap]
  have hJker : ∀ s ∈ J, ρ s = 0 := by
    intro s hs
    rw [hJdef] at hs
    refine Submodule.span_induction (p := fun s _ => ρ s = 0) ?_ ?_ ?_ ?_ hs
    · rintro s ⟨a, ha, rfl⟩
      rw [hρι, (IsLocalRing.residue_eq_zero_iff _).2 ha, map_zero]
    · exact map_zero ρ
    · intro a b _ _ ha hb; rw [map_add, ha, hb, add_zero]
    · intro r s _ hs; rw [smul_eq_mul, map_mul, hs, mul_zero]
  let ρbar : (↥S ⧸ J) →+* Fbar := Ideal.Quotient.lift J ρ hJker
  have hρbar : ∀ s : ↥S, ρbar (Ideal.Quotient.mk J s) = ρ s := fun s => rfl

  obtain ⟨hTR, hT1⟩ := hT
  have hTR' : (⟨(T : F), hTR⟩ : ↥R.integers) = ⟨(T : F), hSR T⟩ := rfl
  have hresT : R.residue ⟨(T : F), hSR T⟩ ≠ 0 := by
    intro h0
    rw [← hTR', h0, Place.ord_zero] at hT1
    exact zero_ne_one hT1
  have hTnu : ¬ IsUnit T := by
    intro hu
    have := ((hUNITS T (hSR T)).1 hu).1
    rw [hTR'] at hT1
    omega
  have hTbar0 : Ideal.Quotient.mk J T ≠ 0 := by
    intro h0
    apply hresT
    rw [← hρ, ← hρbar, h0, map_zero]
  have hTbarm : Ideal.Quotient.mk J T ∈ maximalIdeal (↥S ⧸ J) := map_nonunit (Ideal.Quotient.mk J) T hTnu

  have hinj : Function.Injective ρbar := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hker
    haveI : (RingHom.ker ρbar).IsPrime := RingHom.ker_isPrime ρbar
    have hmax : RingHom.ker ρbar = maximalIdeal _ :=
      IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hker)
    have : Ideal.Quotient.mk J T ∈ RingHom.ker ρbar := hmax ▸ hTbarm
    rw [RingHom.mem_ker, hρbar, hρ] at this
    exact hresT this

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (↥S ⧸ J)
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hTbar0 hϖ

  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective ϖ
  obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective (u : ↥S ⧸ J)
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hpnu : ¬ IsUnit p := fun h => hϖ.not_isUnit (hp ▸ h.map (Ideal.Quotient.mk J))
  have hvu : IsUnit v := by
    by_contra h
    exact (map_nonunit (Ideal.Quotient.mk J) v h) (hv ▸ Units.isUnit u)
  have hordv : Q.ord (R.residue ⟨(v : F), hSR v⟩) = 0 := ((hUNITS v (hSR v)).1 hvu).1
  have hresv0 : R.residue ⟨(v : F), hSR v⟩ ≠ 0 := ((hUNITS v (hSR v)).1 hvu).2
  have hresp0 : R.residue ⟨(p : F), hSR p⟩ ≠ 0 := by
    intro h0
    apply hϖ0
    apply hinj
    rw [← hp, hρbar, hρ, h0, map_zero]
  have hordp : Q.ord (R.residue ⟨(p : F), hSR p⟩) ≠ 0 := fun h0 =>
    hpnu ((hUNITS p (hSR p)).2 ⟨h0, hresp0⟩)
  have hk : k = 1 := by
    have h := congrArg ρbar hu
    rw [map_mul, map_pow, ← hv, ← hp, hρbar, hρbar, hρbar, hρ, hρ, hρ] at h
    have h' := congrArg Q.ord h
    rw [Q.ord_mul hresT hresv0, ← zpow_natCast, Q.ord_zpow, hT1, hordv, add_zero] at h'

    have hk0 : (0 : ℤ) ≤ k := Int.natCast_nonneg k
    have := Int.eq_one_of_mul_eq_one_right hk0 h'.symm
    exact_mod_cast this
  have hassoc : Associated (Ideal.Quotient.mk J T) ϖ := by
    refine ⟨u, ?_⟩; rw [hu, hk, pow_one]
  have hmbar : maximalIdeal (↥S ⧸ J) = Ideal.span {Ideal.Quotient.mk J T} := by
    rw [hϖ.maximalIdeal_eq]
    exact (Ideal.span_singleton_eq_span_singleton.2 hassoc).symm

  refine ⟨ι, hι, hlocS, ?_, ?_, ?_⟩
  ·
    have hcomap : (maximalIdeal (↥S ⧸ J)).comap (Ideal.Quotient.mk J) = maximalIdeal ↥S := by
      ext s
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        mem_nonunits_iff]
      exact ⟨fun h hu => h (hu.map _), fun h => map_nonunit (Ideal.Quotient.mk J) s h⟩
    rw [← hcomap, hmbar, ← Set.image_singleton, ← Ideal.map_span, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_comm]
  ·
    intro hTJ
    exact hTbar0 ((Ideal.Quotient.eq_zero_iff_mem).2 hTJ)
  ·
    intro r
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨b, rfl⟩ := (locEquiv φ x).surjective s
    obtain ⟨a, ha⟩ := hrat b
    refine ⟨a, ?_⟩
    change IsLocalRing.residue ↥S (ι a) = IsLocalRing.residue ↥S (locEquiv φ x b)
    have hι' : ι a = locEquiv φ x (cstHom x a) := rfl
    rw [hι', eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← map_sub]
    intro hu
    exact ha (by have h__af := hu.map (locEquiv φ x).symm.toRingHom; simp at h__af; exact h__af)

end MainCX
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_maximalIdeal_localRing_eq_map_sup_span_of_ord_eq_one_of_mem_smoothLocus.M3aGlue"

end S_AlgebraicCurve_exists_maximalIdeal_localRing_eq_map_sup_span_of_ord_eq_one_of_mem_smoothLocus
end P2MW
export P2MW.S_AlgebraicCurve_exists_maximalIdeal_localRing_eq_map_sup_span_of_ord_eq_one_of_mem_smoothLocus (solution)
