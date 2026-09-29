-- Prove2me | solution 1 for AlgebraicGeometry.exists_localRing_eq_localization_of_normal_affineModel_of_map_maximalIdeal_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/3d98afca-67a4-5a67-824f-ce18e9c012c4

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_eq_closedPoint_and_forall_mem_of_valuationSubring
import Theorems.Thm_AlgebraicGeometry_Scheme_eq_of_forall_mem_valuationSubring_of_isSeparated
import Theorems.Thm_Algebra_QuasiFiniteAt_exists_algebraMap_mul_eq_of_isIntegrallyClosed_of_injective
import Theorems.Thm_Algebra_QuasiFiniteAt_of_minimal_of_maximal
import Theorems.Thm_Subring_isMaximal_of_liesOver_adjoin_of_forall_not_isMaximal_valuationSubring
import Theorems.Thm_IsIntegrallyClosed_isDomain_and_isIntegrallyClosed_of_flat_of_isLocalHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_localRing_eq_localization_of_normal_affineModel_of_map_maximalIdeal_le

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
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_localRing_eq_localization_of_normal_affineModel_of_map_maximalIdeal_le.M3aGlue"

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
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_localRing_eq_localization_of_normal_affineModel_of_map_maximalIdeal_le.M3aGlue"

namespace M3aGlue
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
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_localRing_eq_localization_of_normal_affineModel_of_map_maximalIdeal_le.M3aGlue"

namespace P5Kit

section K1

theorem isFractionRing_of_frac {F₀ : Type} [Field F₀] {A₀ : Type} [CommRing A₀] [Algebra A₀ F₀] (B : Subalgebra A₀ F₀)
    (hBfrac : ∀ x : F₀, ∃ b c : F₀, b ∈ B ∧ c ∈ B ∧ c ≠ 0 ∧ x * c = b) :
    IsFractionRing ↥B.toSubring F₀ where
  map_units := by
    rintro ⟨y, hy⟩
    have hy0 : (y : F₀) ≠ 0 := fun h0 => by
      have : y = 0 := Subtype.ext h0
      exact (mem_nonZeroDivisors_iff_ne_zero.mp hy) this
    exact isUnit_iff_ne_zero.mpr hy0
  surj := by
    intro x
    obtain ⟨b, c, hb, hc, hc0, h⟩ := hBfrac x
    refine ⟨⟨⟨b, hb⟩, ⟨⟨c, hc⟩, mem_nonZeroDivisors_iff_ne_zero.mpr fun h0 => hc0 (congrArg Subtype.val h0)⟩⟩, ?_⟩
    exact h
  exists_of_eq := by
    intro x y h
    exact ⟨1, by rw [Subtype.ext h]⟩

variable {F₀ : Type} [Field F₀] (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsNoetherianRing A₀] [Algebra A₀ F₀]
  (B : Subalgebra A₀ F₀) (𝔭 : Ideal ↥B.toSubring) [𝔭.IsPrime]

theorem mem_ofPrime_iff (f : F₀) :
    f ∈ (LocalSubring.ofPrime B.toSubring 𝔭).toSubring ↔
      ∃ b c : ↥B, (⟨(c : F₀), c.2⟩ : ↥B.toSubring) ∉ 𝔭 ∧ f * (c : F₀) = (b : F₀) := by
  classical
  constructor
  · intro hf
    obtain ⟨⟨b, c⟩, h⟩ := IsLocalization.surj 𝔭.primeCompl (⟨f, hf⟩ : ↥(LocalSubring.ofPrime B.toSubring 𝔭).toSubring)
    refine ⟨⟨(b : F₀), b.2⟩, ⟨((c : ↥B.toSubring) : F₀), (c : ↥B.toSubring).2⟩, c.2, ?_⟩
    have := congrArg (fun w : ↥(LocalSubring.ofPrime B.toSubring 𝔭).toSubring => (w : F₀)) h
    simp at this
    exact this
  · rintro ⟨b, c, hc, h⟩
    have hc0 : (c : F₀) ≠ 0 := by
      intro h0; apply hc
      have : (⟨(c : F₀), c.2⟩ : ↥B.toSubring) = 0 := Subtype.ext h0
      rw [this]; exact zero_mem 𝔭
    have hu : IsUnit (algebraMap ↥B.toSubring ↥(LocalSubring.ofPrime B.toSubring 𝔭).toSubring ⟨(c : F₀), c.2⟩) :=
      IsLocalization.map_units (M := 𝔭.primeCompl) _ ⟨⟨(c : F₀), c.2⟩, hc⟩
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
    have hwc : (w : F₀) = (c : F₀)⁻¹ := by
      have := congrArg (fun z : ↥(LocalSubring.ofPrime B.toSubring 𝔭).toSubring => (z : F₀)) hw
      simp only [Subring.coe_mul, OneMemClass.coe_one] at this
      exact (DivisionMonoid.inv_eq_of_mul _ _ this).symm
    have hf : f = (b : F₀) * (c : F₀)⁻¹ := by rw [← h, mul_assoc, mul_inv_cancel₀ hc0, mul_one]
    rw [hf, ← hwc]
    exact mul_mem (LocalSubring.le_ofPrime B.toSubring 𝔭 b.2) w.2

theorem isFractionRing_ofPrime
    (hBfrac : ∀ x : F₀, ∃ b c : F₀, b ∈ B ∧ c ∈ B ∧ c ≠ 0 ∧ x * c = b) :
    IsFractionRing ↥(LocalSubring.ofPrime B.toSubring 𝔭).toSubring F₀ := by
  classical
  haveI : IsFractionRing ↥B.toSubring F₀ := P5Kit.isFractionRing_of_frac B hBfrac
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.primeCompl
    ↥(LocalSubring.ofPrime B.toSubring 𝔭).toSubring F₀

theorem isIntegrallyClosed_ofPrime
    (hBfrac : ∀ x : F₀, ∃ b c : F₀, b ∈ B ∧ c ∈ B ∧ c ≠ 0 ∧ x * c = b)
    (hBn : ∀ x : F₀, IsIntegral ↥B x → x ∈ B) :
    IsIntegrallyClosed ↥(LocalSubring.ofPrime B.toSubring 𝔭).toSubring := by
  classical
  haveI : IsFractionRing ↥B.toSubring F₀ := P5Kit.isFractionRing_of_frac B hBfrac
  haveI : IsIntegrallyClosed ↥B.toSubring := by
    refine (isIntegrallyClosed_iff F₀).mpr fun {x} hx => ?_
    have hx' : IsIntegral ↥B x := hx
    exact ⟨⟨x, hBn x hx'⟩, rfl⟩
  exact isIntegrallyClosed_of_isLocalization ↥(LocalSubring.ofPrime B.toSubring 𝔭).toSubring 𝔭.primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors 𝔭)

theorem isNoetherianRing_ofPrime (hBfg : B.FG) :
    IsNoetherianRing ↥(LocalSubring.ofPrime B.toSubring 𝔭).toSubring := by
  haveI : Algebra.FiniteType A₀ ↥B := (Subalgebra.fg_iff_finiteType B).mp hBfg
  have hN : IsNoetherianRing ↥B := Algebra.FiniteType.isNoetherianRing A₀ ↥B
  have hN' : IsNoetherianRing ↥B.toSubring := hN
  exact IsLocalization.isNoetherianRing 𝔭.primeCompl _ hN'

theorem mem_maximalIdeal_ofPrime_iff (b : ↥B) :
    (⟨(b : F₀), LocalSubring.le_ofPrime B.toSubring 𝔭 b.2⟩ : ↥(LocalSubring.ofPrime B.toSubring 𝔭).toSubring) ∈
        maximalIdeal ↥(LocalSubring.ofPrime B.toSubring 𝔭).toSubring ↔
      (⟨(b : F₀), b.2⟩ : ↥B.toSubring) ∈ 𝔭 := by
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff ↥(LocalSubring.ofPrime B.toSubring 𝔭).toSubring 𝔭 ⟨(b : F₀), b.2⟩

end K1
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_localRing_eq_localization_of_normal_affineModel_of_map_maximalIdeal_le.M3aGlue"

section K2

theorem mem_localRing_iff_exists_sections
    {F : Type} [Field F] (X : Scheme.{0}) [IsIntegral X] (φ : F ≃+* X.functionField)
    {U : X.Opens} (hU : IsAffineOpen U) (y : X) (hy : y ∈ U) (f : F) :
    let ρ : Γ(X, U) →+* F := φ.symm.toRingHom.comp
      ((algebraMap (X.presheaf.stalk y) X.functionField).comp (X.presheaf.germ U y hy).hom)
    f ∈ SemistableModel.localRing X φ y ↔
      ∃ b c : Γ(X, U), c ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ∧ f * ρ c = ρ b := by
  classical
  dsimp only
  letI alg : Algebra ↑Γ(X, U) ↑(X.presheaf.stalk y) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hy⟩
  haveI hloc : IsLocalization.AtPrime (↑(X.presheaf.stalk y)) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  have halg : ∀ s : Γ(X, U), algebraMap ↑Γ(X, U) ↑(X.presheaf.stalk y) s = (X.presheaf.germ U y hy).hom s := fun _ => rfl
  set g : ↑(X.presheaf.stalk y) →+* ↑X.functionField := algebraMap (X.presheaf.stalk y) X.functionField with hg
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨⟨b, c⟩, h⟩ := IsLocalization.surj (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl s
    refine ⟨b, c, c.2, ?_⟩
    simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, Function.comp_apply]
    rw [← map_mul, ← map_mul, ← halg, ← halg]
    congr 2
  · rintro ⟨b, c, hc, h⟩
    simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, Function.comp_apply] at h
    have hu : IsUnit (algebraMap ↑Γ(X, U) ↑(X.presheaf.stalk y) c) :=
      IsLocalization.map_units (M := (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl) _ ⟨c, hc⟩
    obtain ⟨u, hu'⟩ := hu
    have hgc : g ((X.presheaf.germ U y hy).hom c) = g (u : ↑(X.presheaf.stalk y)) := by rw [hu', halg]
    have hne : φ.symm (g ((X.presheaf.germ U y hy).hom c)) ≠ 0 := by
      rw [hgc]
      exact (map_ne_zero φ.symm).mpr (hu'.symm ▸ (hu'.symm ▸ u.isUnit) |>.map g |>.ne_zero)
    refine ⟨(X.presheaf.germ U y hy).hom b * ((u⁻¹ : (↑(X.presheaf.stalk y))ˣ) : ↑(X.presheaf.stalk y)), ?_⟩
    simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, Function.comp_apply]
    have hf : f = φ.symm (g ((X.presheaf.germ U y hy).hom b)) * (φ.symm (g ((X.presheaf.germ U y hy).hom c)))⁻¹ := by
      rw [← h, mul_assoc, mul_inv_cancel₀ hne, mul_one]
    have hginv : g ((u⁻¹ : (↑(X.presheaf.stalk y))ˣ) : ↑(X.presheaf.stalk y)) = (g (u : ↑(X.presheaf.stalk y)))⁻¹ := by
      symm
      apply DivisionMonoid.inv_eq_of_mul
      rw [← map_mul, Units.mul_inv, map_one]
    rw [map_mul g, hginv, map_mul, map_inv₀, hf, hgc]

end K2
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_localRing_eq_localization_of_normal_affineModel_of_map_maximalIdeal_le.M3aGlue"

end P5Kit
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_localRing_eq_localization_of_normal_affineModel_of_map_maximalIdeal_le.M3aGlue"

namespace M3aGlue

section Centre

variable {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X] {φ : F ≃+* X.functionField}

def IsCentre (φ : F ≃+* X.functionField) (V : ValuationSubring F) (z : X) : Prop :=
  SemistableModel.localRing X φ z ≤ V.toSubring ∧
    ∀ s ∈ maximalIdeal (X.presheaf.stalk z), locHom φ z s ∈ V.nonunits

theorem IsCentre.sub {V : ValuationSubring F} {z : X} (h : IsCentre φ V z) :
    ∀ s : X.presheaf.stalk z, algebraMap (X.presheaf.stalk z) X.functionField s ∈ VK φ V :=
  (forall_mem_VK_iff φ V z).2 h.1

theorem IsCentre.dom {V : ValuationSubring F} {z : X} (h : IsCentre φ V z) :
    ∀ s ∈ maximalIdeal (X.presheaf.stalk z), algebraMap (X.presheaf.stalk z) X.functionField s ∈ (VK φ V).nonunits :=
  fun s hs => (mem_VK_nonunits_iff φ V _).2 (h.2 s hs)

theorem isCentre_of_VK (φ : F ≃+* X.functionField) {V : ValuationSubring F} {z : X}
    (hsub : ∀ s : X.presheaf.stalk z, algebraMap (X.presheaf.stalk z) X.functionField s ∈ VK φ V)
    (hdom : ∀ s ∈ maximalIdeal (X.presheaf.stalk z),
      algebraMap (X.presheaf.stalk z) X.functionField s ∈ (VK φ V).nonunits) : IsCentre φ V z :=
  ⟨(forall_mem_VK_iff φ V z).1 hsub, fun s hs => (mem_VK_nonunits_iff φ V _).1 (hdom s hs)⟩

theorem IsCentre.mem {V : ValuationSubring F} {z : X} (h : IsCentre φ V z) (s : X.presheaf.stalk z) :
    locHom φ z s ∈ V := h.1 (locHom_mem φ z s)

theorem IsCentre.isUnit_iff {V : ValuationSubring F} {z : X} (h : IsCentre φ V z) (s : X.presheaf.stalk z) :
    IsUnit s ↔ IsUnit (⟨locHom φ z s, h.mem s⟩ : ↥V) := by
  constructor
  · intro hu
    let ρ : X.presheaf.stalk z →+* ↥V := (locHom φ z).codRestrict V.toSubring h.mem
    exact hu.map ρ
  · intro hu
    by_contra hs
    have := h.2 s hs
    rw [mem_nonunits_iff_not_isUnit V (h.mem s)] at this
    exact this hu

theorem isCentre_of_localRing_eq {V : ValuationSubring F} {z : X}
    (h : SemistableModel.localRing X φ z = V.toSubring) : IsCentre φ V z := by
  refine ⟨le_of_eq h, fun s hs => ?_⟩
  rw [ValuationSubring.mem_nonunits_iff_or]
  by_cases h0 : locHom φ z s = 0
  · exact Or.inl h0
  · right
    intro hinv
    apply hs
    rw [isUnit_iff_exists_mul_eq_one φ z s]
    refine ⟨(locHom φ z s)⁻¹, ?_, mul_inv_cancel₀ h0⟩
    rw [h]; exact hinv

theorem IsCentre.eq {V : ValuationSubring F} {z₁ z₂ : X} (h₁ : IsCentre φ V z₁)
    {O : Type} [CommRing O] (f : X ⟶ Spec (CommRingCat.of O)) [IsSeparated f]
    (h₂ : IsCentre φ V z₂) : z₁ = z₂ :=
  AlgebraicGeometry.Scheme.eq_of_forall_mem_valuationSubring_of_isSeparated f (VK φ V) z₁ z₂
    h₁.sub h₁.dom h₂.sub h₂.dom

end Centre
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_localRing_eq_localization_of_normal_affineModel_of_map_maximalIdeal_le.M3aGlue"

end M3aGlue
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_localRing_eq_localization_of_normal_affineModel_of_map_maximalIdeal_le.M3aGlue"

section MainP5

open M3aGlue

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

    (B : Subalgebra A₀ F₀) (hBfg : B.FG) (hBn : ∀ x : F₀, _root_.IsIntegral ↥B x → x ∈ B)
    (hBfrac : ∀ x : F₀, ∃ b c : F₀, b ∈ B ∧ c ∈ B ∧ c ≠ 0 ∧ x * c = b)

    (hdimB : ∀ 𝔮 : Ideal ↥B, 𝔮.IsPrime → Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔮 → ¬ 𝔮.IsMaximal →
      𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes)

    (hcomp : ∀ η : X₀, toBase₀.base η = closedPoint A₀ → (∃ y : X₀, η ⤳ y ∧ y ≠ η) →
      (B : Set F₀) ⊆ SemistableModel.localRing X₀ φ₀ η →
        ∃ 𝔮 : Ideal ↥B, 𝔮.IsPrime ∧ ∀ x : F₀, x ∈ SemistableModel.localRing X₀ φ₀ η ↔
          ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : F₀) = (b : F₀))
    (hcomp' : ∀ 𝔮 : Ideal ↥B, 𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes →
      ∃ η : X₀, toBase₀.base η = closedPoint A₀ ∧ (∃ y : X₀, η ⤳ y ∧ y ≠ η) ∧
        ∀ x : F₀, x ∈ SemistableModel.localRing X₀ φ₀ η ↔ ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : F₀) = (b : F₀))
    (𝔭 : Ideal ↥B) [𝔭.IsPrime] (h𝔭 : Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔭) :
    ∃ x : X₀, ∀ f : F₀, f ∈ SemistableModel.localRing X₀ φ₀ x ↔ ∃ b c : ↥B, c ∉ 𝔭 ∧ f * (c : F₀) = (b : F₀) := by
  classical

  by_cases hA : 𝔭 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes
  · obtain ⟨η, -, -, hη⟩ := hcomp' 𝔭 hA
    exact ⟨η, hη⟩

  have h𝔭max : 𝔭.IsMaximal := by
    by_contra h
    exact hA (hdimB 𝔭 inferInstance h𝔭 h)

  let Bp : LocalSubring F₀ := LocalSubring.ofPrime B.toSubring 𝔭
  obtain ⟨V, hV⟩ := Bp.exists_le_valuationSubring

  have hBp_mem : ∀ f : F₀, f ∈ Bp.toSubring ↔ ∃ b c : ↥B, c ∉ 𝔭 ∧ f * (c : F₀) = (b : F₀) :=
    fun f => P5Kit.mem_ofPrime_iff A₀ B 𝔭 f

  obtain ⟨hBpV, hBpVloc⟩ := hV
  have hBBp : ∀ b : ↥B, (b : F₀) ∈ Bp.toSubring := fun b => LocalSubring.le_ofPrime B.toSubring 𝔭 b.2
  have hφ' : ∀ a : A₀, φ₀.symm (SemistableModel.baseToFunctionField toBase₀ a) = algebraMap A₀ F₀ a := fun a => by
    rw [← hφ₀, RingEquiv.symm_apply_apply]
  have hcentre : ∃ x : X₀, toBase₀.base x = closedPoint A₀ ∧ IsCentre φ₀ V x := by
    have hOV : ∀ a : A₀, (X₀.presheaf.germ ⊤ (genericPoint X₀) trivial).hom
        (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv a)) ∈ VK φ₀ V := by
      intro a
      rw [mem_VK_iff]
      change φ₀.symm (SemistableModel.baseToFunctionField toBase₀ a) ∈ V
      rw [hφ']
      exact hBpV (hBBp ⟨algebraMap A₀ F₀ a, B.algebraMap_mem a⟩)
    have hmV : ∀ a ∈ maximalIdeal A₀, (X₀.presheaf.germ ⊤ (genericPoint X₀) trivial).hom
        (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv a)) ∈ (VK φ₀ V).nonunits := by
      intro a ha
      rw [mem_VK_nonunits_iff]
      change φ₀.symm (SemistableModel.baseToFunctionField toBase₀ a) ∈ V.nonunits
      rw [hφ']
      exact (by

        have hb𝔭 : (⟨algebraMap A₀ F₀ a, B.algebraMap_mem a⟩ : ↥B) ∈ 𝔭 := h𝔭 (Ideal.mem_map_of_mem _ ha)
        have h1 := (P5Kit.mem_maximalIdeal_ofPrime_iff A₀ B 𝔭 ⟨algebraMap A₀ F₀ a, B.algebraMap_mem a⟩).2 hb𝔭
        have h2 : ¬ IsUnit (Subring.inclusion hBpV ⟨algebraMap A₀ F₀ a, hBBp ⟨_, B.algebraMap_mem a⟩⟩) :=
          fun hu => ((IsLocalRing.mem_maximalIdeal _).1 h1) (IsLocalHom.map_nonunit _ hu)
        exact (mem_nonunits_iff_not_isUnit V (hBpV (hBBp ⟨_, B.algebraMap_mem a⟩))).2 h2)
    obtain ⟨c, hc, hsub, hdom⟩ :=
      AlgebraicGeometry.Scheme.exists_eq_closedPoint_and_forall_mem_of_valuationSubring toBase₀ (VK φ₀ V) hOV hmV
    exact ⟨c, hc, isCentre_of_VK φ₀ hsub hdom⟩
  obtain ⟨x, hxsp, hxc⟩ := hcentre

  have hunitV : ∀ s : X₀.presheaf.stalk x, locHom φ₀ x s ∉ V.nonunits → IsUnit s := by
    intro s hs
    rw [hxc.isUnit_iff s]
    by_contra hu
    exact hs ((mem_nonunits_iff_not_isUnit V (hxc.mem s)).2 hu)

  have hcV : ∀ c : ↥B, c ∉ 𝔭 → (c : F₀) ∉ V.nonunits := by
    intro c hc hcn
    have hc0 : (c : F₀) ≠ 0 := fun h0 => hc (by
      have : c = 0 := Subtype.ext h0
      rw [this]; exact 𝔭.zero_mem)
    have hinv : (c : F₀)⁻¹ ∈ Bp.toSubring := (hBp_mem _).2 ⟨1, c, hc, by rw [inv_mul_cancel₀ hc0]; simp⟩
    apply (mem_nonunits_iff_not_isUnit V (hBpV (hBBp c))).1 hcn
    exact IsUnit.of_mul_eq_one (b := ⟨(c : F₀)⁻¹, hBpV hinv⟩) (Subtype.ext (mul_inv_cancel₀ hc0))

  have h𝔭V : ∀ b : ↥B, b ∈ 𝔭 → (b : F₀) ∈ V.nonunits := by
    intro b hb
    have h1 := (P5Kit.mem_maximalIdeal_ofPrime_iff A₀ B 𝔭 b).2 hb
    have h2 : ¬ IsUnit (Subring.inclusion hBpV ⟨(b : F₀), hBBp b⟩) :=
      fun hu => ((IsLocalRing.mem_maximalIdeal _).1 h1) (IsLocalHom.map_nonunit _ hu)
    exact (mem_nonunits_iff_not_isUnit V (hBpV (hBBp b))).2 h2

  haveI : IsLocallyNoetherian X₀ := LocallyOfFiniteType.isLocallyNoetherian toBase₀
  haveI hOloc : IsLocalRing ↥(SemistableModel.localRing X₀ φ₀ x) :=
    IsLocalRing.of_surjective' (locEquiv φ₀ x).toRingHom (locEquiv φ₀ x).surjective
  haveI : IsNoetherianRing ↥(SemistableModel.localRing X₀ φ₀ x) :=
    isNoetherianRing_of_ringEquiv _ (locEquiv φ₀ x)
  haveI : IsIntegrallyClosed (X₀.presheaf.stalk x) := hn₀ x
  haveI hlocsymm : IsLocalHom (locEquiv φ₀ x).symm.toRingHom := ⟨fun a ha => by
    have := ha.map (locEquiv φ₀ x).toRingHom
    rwa [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.apply_symm_apply] at this⟩
  obtain ⟨-, hOic⟩ := IsIntegrallyClosed.isDomain_and_isIntegrallyClosed_of_flat_of_isLocalHom
    (locEquiv φ₀ x).symm.toRingHom (RingHom.Flat.of_bijective (locEquiv φ₀ x).symm.bijective)
  haveI := hOic
  haveI : IsFractionRing ↥(SemistableModel.localRing X₀ φ₀ x) F₀ := by
    refine IsFractionRing.of_field _ _ fun z => ?_
    obtain ⟨a, b, hb, hab⟩ := exists_frac_localRing X₀ φ₀ x z
    exact ⟨a, b, (eq_div_iff hb).2 hab⟩

  have hOunit : ∀ g : ↥(SemistableModel.localRing X₀ φ₀ x), IsUnit g ↔ (g : F₀) ∉ V.nonunits := by
    intro g
    obtain ⟨s, hs⟩ := (locEquiv φ₀ x).surjective g
    subst hs
    have h1 : IsUnit ((locEquiv φ₀ x) s) ↔ IsUnit s :=
      ⟨fun h => by simpa using h.map (locEquiv φ₀ x).symm.toRingHom, fun h => h.map (locEquiv φ₀ x).toRingHom⟩
    rw [h1, hxc.isUnit_iff s, coe_locEquiv, mem_nonunits_iff_not_isUnit V (hxc.mem s), not_not]

  have hAO : ∀ a : A₀, algebraMap A₀ F₀ a ∈ SemistableModel.localRing X₀ φ₀ x := by
    intro a
    rw [← hφ', mem_localRing_iff]
    refine ⟨(X₀.presheaf.germ ⊤ x trivial).hom (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv a)), ?_⟩
    rw [locHom_apply]
    change φ₀.symm (algebraMap _ _ ((X₀.presheaf.germ ⊤ x trivial).hom
      (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv a)))) = _
    rw [algebraMap_germ_appTop toBase₀ x a]
  have h3 : (B : Set F₀) ⊆ SemistableModel.localRing X₀ φ₀ x := by

    set O : Subring F₀ := SemistableModel.localRing X₀ φ₀ x with hOdef
    have hOV : O ≤ V.toSubring := hxc.1
    have hBV : (B : Set F₀) ⊆ V := fun f hf => hBpV (hBBp ⟨f, hf⟩)
    let S : Subalgebra ↥O F₀ := Algebra.adjoin ↥O (B : Set F₀)
    let VS : Subalgebra ↥O F₀ := { V.toSubring with algebraMap_mem' := fun o => hOV o.2 }
    have hSVS : S ≤ VS := Algebra.adjoin_le (fun f hf => hBV hf)
    have hSV : ∀ s : ↥S, (s : F₀) ∈ V := fun s => hSVS s.2
    let ιSV : ↥S →+* ↥V :=
      { toFun := fun s => ⟨(s : F₀), hSV s⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
    let ℜ : Ideal ↥S := (maximalIdeal ↥V).comap ιSV
    haveI hℜp : ℜ.IsPrime := Ideal.comap_isPrime ιSV _
    have hmemℜ : ∀ s : ↥S, s ∈ ℜ ↔ (s : F₀) ∈ V.nonunits := by
      intro s
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        mem_nonunits_iff_not_isUnit V (hSV s)]
      rfl

    have hfib : ∀ P : Ideal ↥S, P.IsPrime →
        (∀ g : ↥O, g ∈ maximalIdeal ↥O ↔ algebraMap ↥O ↥S g ∈ P) → P.IsMaximal := by
      intro P hP hPO
      haveI := hP
      refine Subring.isMaximal_of_liesOver_adjoin_of_forall_not_isMaximal_valuationSubring A₀ O hAO ?_ B hBfg ?_ P hPO
      ·
        intro a ha
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hOunit, not_not]
        exact (by

          have hb𝔭 : (⟨algebraMap A₀ F₀ a, B.algebraMap_mem a⟩ : ↥B) ∈ 𝔭 := h𝔭 (Ideal.mem_map_of_mem _ ha)
          have h1 := (P5Kit.mem_maximalIdeal_ofPrime_iff A₀ B 𝔭 ⟨algebraMap A₀ F₀ a, B.algebraMap_mem a⟩).2 hb𝔭
          have h2 : ¬ IsUnit (Subring.inclusion hBpV ⟨algebraMap A₀ F₀ a, hBBp ⟨_, B.algebraMap_mem a⟩⟩) :=
            fun hu => ((IsLocalRing.mem_maximalIdeal _).1 h1) (IsLocalHom.map_nonunit _ hu)
          exact (mem_nonunits_iff_not_isUnit V (hBpV (hBBp ⟨_, B.algebraMap_mem a⟩))).2 h2)
      ·
        intro 𝔮 h𝔮 h𝔮sp h𝔮nm
        haveI := h𝔮
        have h𝔮min := hdimB 𝔮 h𝔮 h𝔮sp h𝔮nm
        obtain ⟨η, hηsp, hηnc, hη⟩ := hcomp' 𝔮 h𝔮min
        obtain ⟨Vq, hVq⟩ := hval η hηsp hηnc
        refine ⟨Vq, fun f => ?_, ?_⟩
        · rw [← hη, ← hVq]; rfl
        · rintro ⟨hOVq, hdomq⟩

          have hxq : IsCentre φ₀ Vq x := by
            refine ⟨hOVq, fun s hs => ?_⟩
            have : (⟨locHom φ₀ x s, locHom_mem φ₀ x s⟩ : ↥O) ∈ maximalIdeal ↥O := by
              rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
              intro hu
              exact hs (hunitV s ((hOunit ⟨_, _⟩).1 hu))
            exact hdomq _ this
          have hηq : IsCentre φ₀ Vq η := isCentre_of_localRing_eq hVq.symm
          have hxη : x = η := hxq.eq toBase₀ hηq

          apply h𝔮nm
          suffices h𝔮𝔭 : 𝔮 = 𝔭 by rw [h𝔮𝔭]; exact h𝔭max
          ext b

          have hbη : (b : F₀) ∈ SemistableModel.localRing X₀ φ₀ η :=
            (hη _).2 ⟨b, 1, fun h1 => h𝔮.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simp⟩
          have hbO : (b : F₀) ∈ O := by rw [hOdef, hxη]; exact hbη
          obtain ⟨s, hs⟩ := (mem_localRing_iff φ₀ x _).1 hbO

          have key1 : b ∈ 𝔭 ↔ ¬ IsUnit s := by
            constructor
            · intro hb hu
              have := h𝔭V b hb
              rw [← hs] at this
              exact (mem_nonunits_iff_not_isUnit V (hxc.mem s)).1 this ((hxc.isUnit_iff s).1 hu)
            · intro hu
              by_contra hb
              exact hu (hunitV s (by rw [hs]; exact hcV b hb))

          have hbVq : (b : F₀) ∈ Vq := by rw [← ValuationSubring.mem_toSubring, hVq]; exact hbη
          have key2 : b ∈ 𝔮 ↔ ¬ IsUnit s := by
            rw [hxq.isUnit_iff s, ← mem_nonunits_iff_not_isUnit Vq (hxq.mem s), hs]
            constructor
            · intro hb

              rw [mem_nonunits_iff_not_isUnit Vq hbVq]
              intro hbu
              have hb0 : (b : F₀) ≠ 0 := fun h0 => by
                apply hbu.ne_zero; exact Subtype.ext h0
              have hinv : (b : F₀)⁻¹ ∈ SemistableModel.localRing X₀ φ₀ η := by
                rw [← hVq, ValuationSubring.mem_toSubring]
                obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hbu
                have : (w : F₀) = (b : F₀)⁻¹ := by
                  have h' := congrArg Subtype.val hw
                  exact eq_inv_of_mul_eq_one_right h'
                rw [← this]; exact w.2
              obtain ⟨b', c, hc, hbc⟩ := (hη _).1 hinv
              apply hc
              have : (c : ↥B) = b * b' := by
                apply Subtype.ext
                change (c : F₀) = (b : F₀) * (b' : F₀)
                rw [← hbc, ← mul_assoc, mul_inv_cancel₀ hb0, one_mul]
              rw [this]; exact 𝔮.mul_mem_right _ hb
            · intro hbn
              by_contra hb
              apply (mem_nonunits_iff_not_isUnit Vq hbVq).1 hbn
              have hb0 : (b : F₀) ≠ 0 := fun h0 => hb (by
                have : b = 0 := Subtype.ext h0
                rw [this]; exact 𝔮.zero_mem)
              have hinv : (b : F₀)⁻¹ ∈ Vq := by
                rw [← ValuationSubring.mem_toSubring, hVq]
                exact (hη _).2 ⟨1, b, hb, by rw [inv_mul_cancel₀ hb0]; simp⟩
              exact IsUnit.of_mul_eq_one (b := ⟨(b : F₀)⁻¹, hinv⟩) (Subtype.ext (mul_inv_cancel₀ hb0))
          exact key2.trans key1.symm

    have hℜO : ∀ g : ↥O, g ∈ maximalIdeal ↥O ↔ algebraMap ↥O ↥S g ∈ ℜ := by
      intro g
      rw [hmemℜ, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hOunit, not_not]
      rfl
    haveI hℜmax : ℜ.IsMaximal := hfib ℜ hℜp hℜO

    haveI : Algebra.FiniteType ↥O ↥S := by
      obtain ⟨t, ht⟩ := hBfg
      rw [← Subalgebra.fg_iff_finiteType]
      refine ⟨t, le_antisymm (Algebra.adjoin_le fun f hf => Algebra.subset_adjoin (ht ▸ Algebra.subset_adjoin hf)) ?_⟩
      apply Algebra.adjoin_le
      intro f hf
      rw [← ht] at hf
      refine Algebra.adjoin_induction (fun y hy => Algebra.subset_adjoin hy) (fun a => ?_)
        (fun _ _ _ _ h1 h2 => add_mem h1 h2) (fun _ _ _ _ h1 h2 => mul_mem h1 h2) hf
      exact Subalgebra.algebraMap_mem (Algebra.adjoin ↥O (t : Set F₀)) (⟨algebraMap A₀ F₀ a, hAO a⟩ : ↥O)
    haveI : Algebra.QuasiFiniteAt ↥O ℜ := by
      have hℜc : ℜ.comap (algebraMap ↥O ↥S) = maximalIdeal ↥O := by
        ext g; rw [Ideal.mem_comap]; exact (hℜO g).symm
      refine Algebra.QuasiFiniteAt.of_minimal_of_maximal ℜ ⟨⟨hℜp, rfl⟩, ?_⟩ ⟨⟨hℜp, rfl⟩, ?_⟩
      · rintro P ⟨hP, hPc⟩ hPℜ
        have hPmax : P.IsMaximal := hfib P hP (fun g => by rw [← Ideal.mem_comap, hPc, hℜc])
        exact (hPmax.eq_of_le hℜmax.ne_top hPℜ).ge
      · rintro P ⟨hP, hPc⟩ hℜP
        exact (hℜmax.eq_of_le hP.ne_top hℜP).ge

    have hSO : ∀ s : ↥S, (s : F₀) ∈ O := by
      intro s
      obtain ⟨a, b, hb, hab⟩ :=
        Algebra.QuasiFiniteAt.exists_algebraMap_mul_eq_of_isIntegrallyClosed_of_injective
          (R := ↥O) (S := ↥S) (K := F₀) Subtype.val_injective ℜ s
      have hbu : IsUnit b := by
        by_contra hbu
        exact hb (by rw [Ideal.mem_comap]; exact (hℜO b).1 ((IsLocalRing.mem_maximalIdeal _).2 hbu))
      have hb0 : (b : F₀) ≠ 0 := fun h0 => hbu.ne_zero (Subtype.ext h0)
      have : (s : F₀) = (a : F₀) * (b : F₀)⁻¹ := by
        have := congrArg (fun u : ↥S => (u : F₀)) hab
        simp only [Subalgebra.coe_mul] at this
        change (b : F₀) * (s : F₀) = (a : F₀) at this
        rw [← this]; field_simp
      rw [this]
      refine O.mul_mem a.2 ?_
      have hinv : ((hbu.unit⁻¹ : (↥O)ˣ) : ↥O) = ((b : F₀)⁻¹ : F₀) := by
        apply eq_inv_of_mul_eq_one_left
        have h1 : ((hbu.unit⁻¹ : (↥O)ˣ) : ↥O) * b = 1 := hbu.val_inv_mul
        exact_mod_cast congrArg Subtype.val h1
      rw [← hinv]; exact Subtype.mem _
    intro f hf
    exact hSO ⟨f, Algebra.subset_adjoin hf⟩

  have h4 : SemistableModel.localRing X₀ φ₀ x ≤ Bp.toSubring := by

    by_cases hex : ∃ y : X₀, toBase₀.base y = closedPoint A₀ ∧ (∃ z : X₀, y ⤳ z ∧ z ≠ y) ∧
        SemistableModel.localRing X₀ φ₀ y = Bp.toSubring
    · obtain ⟨y, -, -, hyBp⟩ := hex
      have hyV : IsCentre φ₀ V y := by
        refine ⟨hyBp ▸ hBpV, fun s hs => ?_⟩
        have hmem : locHom φ₀ y s ∈ Bp.toSubring := hyBp ▸ locHom_mem φ₀ y s
        have hnu : ¬ IsUnit (⟨locHom φ₀ y s, hmem⟩ : ↥Bp.toSubring) := by
          intro hu; apply hs
          rw [isUnit_iff_exists_mul_eq_one φ₀ y s]
          obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hu
          exact ⟨(w : F₀), by rw [hyBp]; exact w.2, congrArg Subtype.val hw⟩
        have h2 : ¬ IsUnit (Subring.inclusion hBpV ⟨locHom φ₀ y s, hmem⟩) :=
          fun hu => hnu (IsLocalHom.map_nonunit _ hu)
        exact (mem_nonunits_iff_not_isUnit V (hBpV hmem)).2 h2
      rw [hxc.eq toBase₀ hyV, hyBp]

    haveI : IsNoetherianRing ↥Bp.toSubring := P5Kit.isNoetherianRing_ofPrime A₀ B 𝔭 hBfg
    haveI : IsIntegrallyClosed ↥Bp.toSubring := P5Kit.isIntegrallyClosed_ofPrime A₀ B 𝔭 hBfrac hBn
    haveI : IsFractionRing ↥Bp.toSubring F₀ := P5Kit.isFractionRing_ofPrime A₀ B 𝔭 hBfrac
    have hAO' : ∀ a : A₀, algebraMap A₀ F₀ a ∈ Bp.toSubring := fun a => hBBp ⟨_, B.algebraMap_mem a⟩
    have hAO'loc : ∀ a : A₀, a ∈ maximalIdeal A₀ →
        (⟨algebraMap A₀ F₀ a, hAO' a⟩ : ↥Bp.toSubring) ∈ maximalIdeal ↥Bp.toSubring := fun a ha =>
      (P5Kit.mem_maximalIdeal_ofPrime_iff A₀ B 𝔭 ⟨algebraMap A₀ F₀ a, B.algebraMap_mem a⟩).2
        (h𝔭 (Ideal.mem_map_of_mem _ ha))

    have hO'unit : ∀ g : ↥Bp.toSubring, IsUnit g ↔ (g : F₀) ∉ V.nonunits := by
      intro g
      rw [mem_nonunits_iff_not_isUnit V (hBpV g.2), not_not]
      constructor
      · intro hu; exact hu.map (Subring.inclusion hBpV)
      · intro hu
        have : IsUnit (Subring.inclusion hBpV g) := hu
        exact IsLocalHom.map_nonunit _ this

    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X₀.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have hle' : U ≤ toBase₀ ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of A₀)).Opens) := le_top
    have hgenU : genericPoint X₀ ∈ U := (genericPoint_spec X₀).mem_open_set_iff U.2 |>.2 ⟨x, Set.mem_univ _, hxU⟩

    let ρ : Γ(X₀, U) →+* F₀ := φ₀.symm.toRingHom.comp
      ((algebraMap (X₀.presheaf.stalk x) X₀.functionField).comp (X₀.presheaf.germ U x hxU).hom)
    have hρ : ∀ (y : X₀) (hy : y ∈ U) (c : Γ(X₀, U)),
        φ₀.symm (algebraMap (X₀.presheaf.stalk y) X₀.functionField ((X₀.presheaf.germ U y hy).hom c)) = ρ c := by
      intro y hy c
      change φ₀.symm ((X₀.presheaf.germ U y hy ≫ X₀.presheaf.stalkSpecializes ((genericPoint_spec X₀).specializes trivial)).hom c) =
        φ₀.symm ((X₀.presheaf.germ U x hxU ≫ X₀.presheaf.stalkSpecializes ((genericPoint_spec X₀).specializes trivial)).hom c)
      rw [TopCat.Presheaf.germ_stalkSpecializes, TopCat.Presheaf.germ_stalkSpecializes]
    have hρloc : ∀ c, ρ c = locHom φ₀ x ((X₀.presheaf.germ U x hxU).hom c) := fun c => by rw [locHom_apply]; rfl
    have hρinj : Function.Injective ρ := by
      intro a b h
      apply AlgebraicGeometry.germ_injective_of_isIntegral (X := X₀) x hxU
      exact locHom_injective φ₀ x (by rw [← hρloc, ← hρloc, h])

    let fAC : A₀ →+* Γ(X₀, U) := (toBase₀.appLE ⊤ U hle').hom.comp (Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom
    letI algAC : Algebra A₀ Γ(X₀, U) := fAC.toAlgebra
    have hρA : ∀ a : A₀, ρ (fAC a) = algebraMap A₀ F₀ a := by
      intro a
      rw [← hφ', hρloc, locHom_apply]
      congr 1
      change algebraMap _ _ ((X₀.presheaf.germ U x hxU).hom ((X₀.presheaf.map (homOfLE hle').op).hom
        (toBase₀.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv a)))) = _
      rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]
      exact algebraMap_germ_appTop toBase₀ x a
    let ρₐ : Γ(X₀, U) →ₐ[A₀] F₀ := { toRingHom := ρ, commutes' := hρA }
    let C : Subalgebra A₀ F₀ := ρₐ.range
    have hCfg : C.FG := by
      have h1 : (toBase₀.appLE ⊤ U hle').hom.FinitePresentation :=
        HasRingHomProperty.appLE @LocallyOfFinitePresentation toBase₀ inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ hle'
      have h2 : (Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom.FinitePresentation :=
        RingHom.FinitePresentation.of_bijective (Scheme.ΓSpecIso (CommRingCat.of A₀)).symm.commRingCatIsoToRingEquiv.bijective
      haveI : Algebra.FiniteType A₀ Γ(X₀, U) := RingHom.FiniteType.of_finitePresentation (h1.comp h2)
      rw [show C = (⊤ : Subalgebra A₀ Γ(X₀, U)).map ρₐ from (Algebra.map_top ρₐ).symm]
      exact Subalgebra.FG.map _ Algebra.FiniteType.out
    have hCmem : ∀ c : Γ(X₀, U), ρ c ∈ C := fun c => ⟨c, rfl⟩
    have hCx : (C : Set F₀) ⊆ SemistableModel.localRing X₀ φ₀ x := by
      rintro f ⟨c, rfl⟩
      change ρ c ∈ _
      rw [hρloc]; exact locHom_mem φ₀ x _

    let ρr : Γ(X₀, U) →ₐ[A₀] ↥C := ρₐ.rangeRestrict
    have hρr : ∀ c, ((ρr c : ↥C) : F₀) = ρ c := fun c => rfl
    have hρrsurj : Function.Surjective ρr := AlgHom.rangeRestrict_surjective ρₐ
    have hcompC : ∀ 𝔮' : Ideal ↥C, 𝔮'.IsPrime → Ideal.map (algebraMap A₀ ↥C) (maximalIdeal A₀) ≤ 𝔮' → ¬ 𝔮'.IsMaximal →
        ∃ V' : ValuationSubring F₀,
          (∀ f : F₀, f ∈ V' ↔ ∃ b c : ↥C, c ∉ 𝔮' ∧ f * (c : F₀) = (b : F₀)) ∧
          ¬ (Bp.toSubring ≤ V'.toSubring ∧ ∀ g : ↥Bp.toSubring, g ∈ maximalIdeal ↥Bp.toSubring → (g : F₀) ∈ V'.nonunits) := by
      intro 𝔮' h𝔮' h𝔮'sp h𝔮'nm
      haveI := h𝔮'
      let P0 : Ideal Γ(X₀, U) := 𝔮'.comap ρr.toRingHom
      haveI hP0 : P0.IsPrime := Ideal.comap_isPrime _ _
      let p0 : PrimeSpectrum Γ(X₀, U) := ⟨P0, hP0⟩
      let y : X₀ := hU.fromSpec.base p0
      have hyU : y ∈ U := by
        have : y ∈ Set.range hU.fromSpec.base := ⟨p0, rfl⟩
        rwa [hU.range_fromSpec] at this
      letI algy := TopCat.Presheaf.algebra_section_stalk X₀.presheaf (⟨y, hyU⟩ : U)
      haveI hlocy : IsLocalization.AtPrime (X₀.presheaf.stalk y) P0 := hU.isLocalization_stalk' p0 hyU
      have hp0 : hU.primeIdealOf ⟨y, hyU⟩ = p0 := by
        have h1 : (⟨y, hyU⟩ : U) = hU.isoSpec.inv.base p0 := rfl
        change hU.isoSpec.hom.base ⟨y, hyU⟩ = p0
        rw [h1, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
        rfl

      have hysp : toBase₀.base y = closedPoint A₀ := by
        apply PrimeSpectrum.ext
        have hle𝔪 : maximalIdeal A₀ ≤ (toBase₀.base y).asIdeal := by
          intro a ha
          by_contra hna
          have hu : IsUnit ((X₀.presheaf.germ ⊤ y trivial).hom
              (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv a))) :=
            (isUnit_germ_appTop_iff toBase₀ y a).2 hna
          have hgerm : (X₀.presheaf.germ U y hyU).hom (fAC a) =
              (X₀.presheaf.germ ⊤ y trivial).hom (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv a)) := by
            change (X₀.presheaf.germ U y hyU).hom ((X₀.presheaf.map (homOfLE hle').op).hom
              (toBase₀.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv a))) = _
            rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]
            rfl
          have hmem : fAC a ∈ P0 := by
            change ρr (fAC a) ∈ 𝔮'
            have : ρr (fAC a) = algebraMap A₀ ↥C a := Subtype.ext (hρA a)
            rw [this]; exact h𝔮'sp (Ideal.mem_map_of_mem _ ha)
          have := (IsLocalization.AtPrime.to_map_mem_maximal_iff (X₀.presheaf.stalk y) P0 (fAC a)).2 hmem
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at this
          apply this
          change IsUnit ((X₀.presheaf.germ U y hyU).hom (fAC a))
          rw [hgerm]; exact hu
        exact ((IsLocalRing.maximalIdeal.isMaximal A₀).eq_of_le (toBase₀.base y).isPrime.ne_top hle𝔪).symm

      have hP0nm : ¬ P0.IsMaximal := by
        intro hm
        apply h𝔮'nm
        have hmap : Ideal.map ρr.toRingHom P0 = 𝔮' := Ideal.map_comap_of_surjective _ hρrsurj _
        rcases Ideal.map_eq_top_or_isMaximal_of_surjective ρr.toRingHom hρrsurj hm with h | h
        · exact absurd (hmap ▸ h) h𝔮'.ne_top
        · exact hmap ▸ h
      obtain ⟨M, hM, hP0M⟩ := Ideal.exists_le_maximal P0 hP0.ne_top
      have hP0neM : P0 ≠ M := fun h => hP0nm (h ▸ hM)
      let m : PrimeSpectrum Γ(X₀, U) := ⟨M, hM.isPrime⟩
      have hyz : y ⤳ hU.fromSpec.base m :=
        ((PrimeSpectrum.le_iff_specializes p0 m).1 hP0M).map hU.fromSpec.base.hom.continuous
      have hzy : hU.fromSpec.base m ≠ y := by
        intro h
        apply hP0neM
        have := hU.fromSpec.isOpenEmbedding.injective h
        exact (congrArg PrimeSpectrum.asIdeal this).symm
      obtain ⟨V', hV'⟩ := hval y hysp ⟨_, hyz, hzy⟩
      refine ⟨V', fun f => ?_, ?_⟩
      ·
        have hK2 : f ∈ SemistableModel.localRing X₀ φ₀ y ↔ ∃ b c : Γ(X₀, U), c ∉ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal ∧
            f * φ₀.symm (algebraMap (X₀.presheaf.stalk y) X₀.functionField ((X₀.presheaf.germ U y hyU).hom c)) =
              φ₀.symm (algebraMap (X₀.presheaf.stalk y) X₀.functionField ((X₀.presheaf.germ U y hyU).hom b)) :=
          P5Kit.mem_localRing_iff_exists_sections X₀ φ₀ hU y hyU f
        rw [← ValuationSubring.mem_toSubring, hV', hK2, hp0]
        constructor
        · rintro ⟨b, c, hc, hbc⟩
          refine ⟨ρr b, ρr c, hc, ?_⟩
          rw [hρr, hρr, ← hρ y hyU c, ← hρ y hyU b]
          exact hbc
        · rintro ⟨b', c', hc', hbc'⟩
          obtain ⟨b, rfl⟩ := hρrsurj b'
          obtain ⟨c, rfl⟩ := hρrsurj c'
          refine ⟨b, c, hc', ?_⟩
          rw [hρ y hyU c, hρ y hyU b]
          exact hbc'
      · rintro ⟨hO'V', hdom'⟩
        apply hex

        have hBy : (B : Set F₀) ⊆ SemistableModel.localRing X₀ φ₀ y := fun f hf => hV' ▸ hO'V' (hBBp ⟨f, hf⟩)
        obtain ⟨𝔮B, h𝔮B, hyB⟩ := hcomp y hysp ⟨_, hyz, hzy⟩ hBy
        haveI := h𝔮B
        have h𝔭𝔮B : 𝔭 ≤ 𝔮B := by
          intro b hb
          by_contra hbq
          have hb0 : (b : F₀) ≠ 0 := fun h0 => hbq (by
            have : b = 0 := Subtype.ext h0
            rw [this]; exact 𝔮B.zero_mem)
          have hinv : (b : F₀)⁻¹ ∈ V' := by
            rw [← ValuationSubring.mem_toSubring, hV']
            exact (hyB _).2 ⟨1, b, hbq, by rw [inv_mul_cancel₀ hb0]; simp⟩
          have hbV' : (b : F₀) ∈ V' := by
            rw [← ValuationSubring.mem_toSubring, hV']; exact hBy b.2
          have hnu := hdom' ⟨(b : F₀), hBBp b⟩ ((P5Kit.mem_maximalIdeal_ofPrime_iff A₀ B 𝔭 b).2 hb)
          apply (mem_nonunits_iff_not_isUnit V' hbV').1 hnu
          exact IsUnit.of_mul_eq_one (b := ⟨(b : F₀)⁻¹, hinv⟩) (Subtype.ext (mul_inv_cancel₀ hb0))
        have h𝔮B𝔭 : 𝔮B = 𝔭 := (h𝔭max.eq_of_le h𝔮B.ne_top h𝔭𝔮B).symm
        refine ⟨y, hysp, ⟨_, hyz, hzy⟩, ?_⟩
        ext f
        rw [hyB, hBp_mem, h𝔮B𝔭]

    set O' : Subring F₀ := Bp.toSubring with hO'def
    let S' : Subalgebra ↥O' F₀ := Algebra.adjoin ↥O' (C : Set F₀)
    let VS' : Subalgebra ↥O' F₀ := { V.toSubring with algebraMap_mem' := fun o => hBpV o.2 }
    have hS'VS : S' ≤ VS' := Algebra.adjoin_le (fun f hf => hxc.1 (hCx hf))
    have hS'V : ∀ s : ↥S', (s : F₀) ∈ V := fun s => hS'VS s.2
    let ιS'V : ↥S' →+* ↥V :=
      { toFun := fun s => ⟨(s : F₀), hS'V s⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
    let ℜ' : Ideal ↥S' := (maximalIdeal ↥V).comap ιS'V
    haveI hℜ'p : ℜ'.IsPrime := Ideal.comap_isPrime ιS'V _
    have hmemℜ' : ∀ s : ↥S', s ∈ ℜ' ↔ (s : F₀) ∈ V.nonunits := by
      intro s
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        mem_nonunits_iff_not_isUnit V (hS'V s)]
      rfl
    have hfib' : ∀ P : Ideal ↥S', P.IsPrime →
        (∀ g : ↥O', g ∈ maximalIdeal ↥O' ↔ algebraMap ↥O' ↥S' g ∈ P) → P.IsMaximal := by
      intro P hP hPO
      haveI := hP
      exact Subring.isMaximal_of_liesOver_adjoin_of_forall_not_isMaximal_valuationSubring A₀ O' hAO' hAO'loc
        C hCfg hcompC P hPO
    have hℜ'O' : ∀ g : ↥O', g ∈ maximalIdeal ↥O' ↔ algebraMap ↥O' ↥S' g ∈ ℜ' := by
      intro g
      rw [hmemℜ', IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hO'unit, not_not]
      rfl
    haveI hℜ'max : ℜ'.IsMaximal := hfib' ℜ' hℜ'p hℜ'O'
    haveI : Algebra.FiniteType ↥O' ↥S' := by
      obtain ⟨t, ht⟩ := hCfg
      rw [← Subalgebra.fg_iff_finiteType]
      refine ⟨t, le_antisymm (Algebra.adjoin_le fun f hf => Algebra.subset_adjoin (ht ▸ Algebra.subset_adjoin hf)) ?_⟩
      apply Algebra.adjoin_le
      intro f hf
      rw [← ht] at hf
      refine Algebra.adjoin_induction (fun y hy => Algebra.subset_adjoin hy) (fun a => ?_)
        (fun _ _ _ _ h1 h2 => add_mem h1 h2) (fun _ _ _ _ h1 h2 => mul_mem h1 h2) hf
      exact Subalgebra.algebraMap_mem (Algebra.adjoin ↥O' (t : Set F₀)) (⟨algebraMap A₀ F₀ a, hAO' a⟩ : ↥O')
    haveI : Algebra.QuasiFiniteAt ↥O' ℜ' := by
      have hℜc : ℜ'.comap (algebraMap ↥O' ↥S') = maximalIdeal ↥O' := by
        ext g; rw [Ideal.mem_comap]; exact (hℜ'O' g).symm
      refine Algebra.QuasiFiniteAt.of_minimal_of_maximal ℜ' ⟨⟨hℜ'p, rfl⟩, ?_⟩ ⟨⟨hℜ'p, rfl⟩, ?_⟩
      · rintro P ⟨hP, hPc⟩ hPℜ
        have hPmax : P.IsMaximal := hfib' P hP (fun g => by rw [← Ideal.mem_comap, hPc, hℜc])
        exact (hPmax.eq_of_le hℜ'max.ne_top hPℜ).ge
      · rintro P ⟨hP, hPc⟩ hℜP
        exact (hℜ'max.eq_of_le hP.ne_top hℜP).ge
    have hS'O' : ∀ s : ↥S', (s : F₀) ∈ O' := by
      intro s
      obtain ⟨a, b, hb, hab⟩ :=
        Algebra.QuasiFiniteAt.exists_algebraMap_mul_eq_of_isIntegrallyClosed_of_injective
          (R := ↥O') (S := ↥S') (K := F₀) Subtype.val_injective ℜ' s
      have hbu : IsUnit b := by
        by_contra hbu
        exact hb (by rw [Ideal.mem_comap]; exact (hℜ'O' b).1 ((IsLocalRing.mem_maximalIdeal _).2 hbu))
      have hb0 : (b : F₀) ≠ 0 := fun h0 => hbu.ne_zero (Subtype.ext h0)
      have : (s : F₀) = (a : F₀) * (b : F₀)⁻¹ := by
        have := congrArg (fun u : ↥S' => (u : F₀)) hab
        simp only [Subalgebra.coe_mul] at this
        change (b : F₀) * (s : F₀) = (a : F₀) at this
        rw [← this]; field_simp
      rw [this]
      refine O'.mul_mem a.2 ?_
      have hinv : ((hbu.unit⁻¹ : (↥O')ˣ) : ↥O') = ((b : F₀)⁻¹ : F₀) := by
        apply eq_inv_of_mul_eq_one_left
        have h1 : ((hbu.unit⁻¹ : (↥O')ˣ) : ↥O') * b = 1 := hbu.val_inv_mul
        exact_mod_cast congrArg Subtype.val h1
      rw [← hinv]; exact Subtype.mem _
    have hCO' : (C : Set F₀) ⊆ O' := fun f hf => hS'O' ⟨f, Algebra.subset_adjoin hf⟩

    intro f hf
    have hK2x : f ∈ SemistableModel.localRing X₀ φ₀ x ↔ ∃ b c : Γ(X₀, U), c ∉ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ∧
        f * ρ c = ρ b := P5Kit.mem_localRing_iff_exists_sections X₀ φ₀ hU x hxU f
    obtain ⟨b, c, hc, hbc⟩ := hK2x.1 hf
    letI algx := TopCat.Presheaf.algebra_section_stalk X₀.presheaf (⟨x, hxU⟩ : U)
    haveI hlocx : IsLocalization.AtPrime (X₀.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
      hU.isLocalization_stalk ⟨x, hxU⟩
    have hcu : IsUnit ((X₀.presheaf.germ U x hxU).hom c) :=
      IsLocalization.map_units (M := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl) (X₀.presheaf.stalk x) ⟨c, hc⟩
    have hρcV : ρ c ∉ V.nonunits := by
      rw [hρloc, mem_nonunits_iff_not_isUnit V (hxc.mem _), not_not, ← hxc.isUnit_iff]
      exact hcu
    have hρcO' : IsUnit (⟨ρ c, hCO' (hCmem c)⟩ : ↥O') := (hO'unit _).2 hρcV
    have hc0 : ρ c ≠ 0 := fun h0 => hρcO'.ne_zero (Subtype.ext h0)
    have hf' : f = ρ b * (ρ c)⁻¹ := by rw [← hbc, mul_inv_cancel_right₀ hc0]
    rw [hf']
    refine O'.mul_mem (hCO' (hCmem b)) ?_
    have hinv : ((hρcO'.unit⁻¹ : (↥O')ˣ) : ↥O') = ((ρ c)⁻¹ : F₀) := by
      apply eq_inv_of_mul_eq_one_left
      have h1 : ((hρcO'.unit⁻¹ : (↥O')ˣ) : ↥O') * ⟨ρ c, hCO' (hCmem c)⟩ = 1 := hρcO'.val_inv_mul
      have h2 := congrArg Subtype.val h1
      exact h2
    rw [← hinv]; exact Subtype.mem _

  have h3' : Bp.toSubring ≤ SemistableModel.localRing X₀ φ₀ x := by
    intro f hf
    obtain ⟨b, c, hc, hbc⟩ := (hBp_mem f).1 hf
    obtain ⟨s, hs⟩ := (mem_localRing_iff φ₀ x _).1 (h3 c.2)
    obtain ⟨t, ht⟩ := (mem_localRing_iff φ₀ x _).1 (h3 b.2)
    have hsU : IsUnit s := hunitV s (by rw [hs]; exact hcV c hc)
    have hc0 : (c : F₀) ≠ 0 := by rw [← hs]; exact fun h0 => hsU.ne_zero (locHom_injective φ₀ x (by rw [h0, map_zero]))
    have hf' : f = (b : F₀) * (c : F₀)⁻¹ := by rw [← hbc, mul_inv_cancel_right₀ hc0]
    rw [hf', mem_localRing_iff]
    refine ⟨t * ↑(hsU.unit⁻¹), ?_⟩
    rw [map_mul, ht, ← hs]
    congr 1
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, IsUnit.val_inv_mul, map_one]
  refine ⟨x, fun f => ?_⟩
  rw [← hBp_mem]
  exact ⟨fun hf => h4 hf, fun hf => h3' hf⟩

end MainP5
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_localRing_eq_localization_of_normal_affineModel_of_map_maximalIdeal_le.M3aGlue"

end S_AlgebraicGeometry_exists_localRing_eq_localization_of_normal_affineModel_of_map_maximalIdeal_le
end P2MW
export P2MW.S_AlgebraicGeometry_exists_localRing_eq_localization_of_normal_affineModel_of_map_maximalIdeal_le (solution)
