-- Prove2me | solution 1 for AlgebraicGeometry.isIntegrallyClosed_stalk_pullback_of_ringEquiv_adicCompletion_stalk_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/7292b84d-d06f-5f6b-a93b-b0e5853908f4

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_AlgebraicCurve_exists_level_mem_functionField_of_iso_pullback_of_isAlgebraic_min
import Theorems.Thm_AlgebraicCurve_flat_fst_and_forall_isPrime_eq_comap_maximalIdeal_of_isPullback_of_ringEquiv_adicCompletion_stalk_min
import Theorems.Thm_AlgebraicCurve_isNoetherianRing_stalk_and_two_le_ringKrullDim_and_exists_eq_mul_pow_of_isPullback_of_ringEquiv_adicCompletion_stalk_min
import Theorems.Thm_AlgebraicCurve_forall_exists_not_isUnit_sub_germ_and_maximalIdeal_le_map_sup_span_of_isPullback_of_ringEquiv_adicCompletion_stalk_min
import Theorems.Thm_IsLocalRing_exists_ringEquiv_adicCompletion_uvCrossingModel_of_isLocalHom_of_layer
import Theorems.Thm_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow
import Theorems.Thm_IsIntegrallyClosed_isDomain_and_isIntegrallyClosed_of_flat_of_isLocalHom
import Theorems.Thm_IsLocalRing_mem_range_algebraMap_of_flat_of_isLocalHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIntegrallyClosed_stalk_pullback_of_ringEquiv_adicCompletion_stalk_of_isDiscreteValuationRing
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry ModularCurve ModularCurve.UVCrossingModel

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

namespace M3aGlue

theorem mem_range_of_isIntegrallyClosed_level
    {R₁ R K₁ K : Type*} [CommRing R₁] [IsDomain R₁] [CommRing R] [IsDomain R] [Field K₁] [Field K]
    [Algebra R₁ K₁] [IsFractionRing R₁ K₁] [Algebra R K] [IsFractionRing R K]
    [Algebra K₁ K] [Algebra R₁ K] [IsScalarTower R₁ K₁ K]
    (f : R₁ →+* R) (hcomm : ∀ r : R₁, algebraMap R K (f r) = algebraMap R₁ K r)
    (hic : IsIntegrallyClosed R₁)
    (p : Polynomial R₁) (hp : p.Monic) (u : K₁)
    (hroot : Polynomial.eval₂ (algebraMap R₁ K) (algebraMap K₁ K u) p = 0) :
    ∃ r : R₁, algebraMap R K (f r) = algebraMap K₁ K u := by
  classical
  haveI := hic

  have hroot₁ : Polynomial.eval₂ (algebraMap R₁ K₁) u p = 0 := by
    apply (algebraMap K₁ K).injective
    rw [Polynomial.hom_eval₂, map_zero, ← hroot]
    congr 1
    ext r
    exact (IsScalarTower.algebraMap_apply R₁ K₁ K r).symm
  have hint : IsIntegral R₁ u := ⟨p, hp, hroot₁⟩
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  refine ⟨r, ?_⟩
  rw [hcomm, ← hr, ← IsScalarTower.algebraMap_apply]

theorem exists_map_eq_of_forall_coeff_mem_range
    {R₁ R K₁ K : Type*} [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field K₁] [Field K]
    [Algebra R₁ K₁] [IsFractionRing R₁ K₁] [Algebra R K] [IsFractionRing R K]
    [Algebra K₁ K] [Algebra R₁ K] [IsScalarTower R₁ K₁ K]
    (f : R₁ →+* R) (hf : f.Flat) [IsLocalHom f] (hcomm : ∀ r : R₁, algebraMap R₁ K r = algebraMap R K (f r))
    (q : Polynomial R) (hq : q.Monic)
    (hcoeff : ∀ i : ℕ, algebraMap R K (q.coeff i) ∈ (algebraMap K₁ K).range) :
    ∃ p : Polynomial R₁, p.Monic ∧ p.map f = q := by
  classical
  have hcoeffR₁ : ∀ i : ℕ, q.coeff i ∈ Set.range f := by
    intro i

    obtain ⟨y, hy⟩ := hcoeff i
    have hy' : algebraMap K₁ K y ∈ (algebraMap R K).range := ⟨q.coeff i, hy.symm⟩
    obtain ⟨r, hr⟩ := IsLocalRing.mem_range_algebraMap_of_flat_of_isLocalHom f hf K₁ K hcomm y hy'
    refine ⟨r, ?_⟩
    apply IsFractionRing.injective R K
    rw [← hcomm, IsScalarTower.algebraMap_apply R₁ K₁ K, hr, hy]
  have hlifts : q ∈ Polynomial.lifts f := (Polynomial.lifts_iff_coeff_lifts q).mpr hcoeffR₁
  obtain ⟨p, hp, -, hpm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hq
  exact ⟨p, hpm, hp⟩

end M3aGlue

section MainNL

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
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase)

    (y : X) (hy : toBase.base y = closedPoint ↥A) (hyc : ∀ z : X, y ⤳ z → z = y)

    (hbranch : ∃ η : X, η ⤳ y ∧ η ≠ y ∧ toBase.base η = closedPoint ↥A)
    (y₀ : X₀) (hy₀ : (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base y = y₀)
    [IsNoetherianRing (X₀.presheaf.stalk y₀)]
    (w : ℕ) (hw : 1 ≤ w)
    (e : AdicCompletion (maximalIdeal (X₀.presheaf.stalk y₀)) (X₀.presheaf.stalk y₀) ≃+*
        (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A₀) A₀) ⧸
          Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A₀) A₀)) * MvPowerSeries.X 1 -
            MvPowerSeries.C ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w)}))
    (he : ∀ a : A₀,
      e (algebraMap (X₀.presheaf.stalk y₀) _
          ((X₀.presheaf.germ ⊤ y₀ trivial).hom (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))) =
        Ideal.Quotient.mk _ (MvPowerSeries.C (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) a))) :
    IsIntegrallyClosed (X.presheaf.stalk y) := by
  classical
  subst hy₀

  rw [isIntegrallyClosed_iff_isIntegrallyClosedIn X.functionField, isIntegrallyClosedIn_iff]
  refine ⟨IsFractionRing.injective _ _, fun {t} ht => ?_⟩
  obtain ⟨q, hq, hqt⟩ := ht

  set d : ℕ := q.natDegree with hd
  let fam : Fin (d + 2) → X.functionField := fun i =>
    Fin.cases t (fun j => algebraMap (X.presheaf.stalk y) X.functionField (q.coeff j)) i
  obtain ⟨A₁, _instA₁, _instD₁, _instDVR₁, ι₁', _instL₁', ι₁, _instL₁, hι₁, hcomp, ϖ₁, hϖ₁, X₁, _instI₁, f₁, g₁, hsq,
      e₁, he₁, he₁', hgen, u, hu⟩ :=
    AlgebraicCurve.exists_level_mem_functionField_of_iso_pullback_of_isAlgebraic_min A hrk X toBase A₀ ι hι ϖ₀ hϖ₀ halg X₀ toBase₀ iso hiso
      y hy hyc ((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base y) rfl w hw e he fam

  obtain ⟨hg₁y, hflat, -⟩ :=
    AlgebraicCurve.flat_fst_and_forall_isPrime_eq_comap_maximalIdeal_of_isPullback_of_ringEquiv_adicCompletion_stalk_min A hrk X toBase A₀ ι hι ϖ₀ hϖ₀ halg X₀ toBase₀ iso hiso
      y hy hyc ((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base y) rfl w hw e he
      A₁ ι₁' ι₁ hι₁ hcomp ϖ₁ hϖ₁ X₁ f₁ g₁ hsq e₁ he₁ he₁'
  obtain ⟨hnoeth₁, hdim₁, e', vv, hvv, hvve⟩ :=
    AlgebraicCurve.isNoetherianRing_stalk_and_two_le_ringKrullDim_and_exists_eq_mul_pow_of_isPullback_of_ringEquiv_adicCompletion_stalk_min A hrk X toBase A₀ ι hι ϖ₀ hϖ₀ halg X₀ toBase₀ iso hiso
      y hy hyc hbranch ((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base y) rfl w hw e he
      A₁ ι₁' ι₁ hι₁ hcomp ϖ₁ hϖ₁ X₁ f₁ g₁ hsq e₁ he₁ he₁'
  obtain ⟨hres₁, hmgen₁⟩ :=
    AlgebraicCurve.forall_exists_not_isUnit_sub_germ_and_maximalIdeal_le_map_sup_span_of_isPullback_of_ringEquiv_adicCompletion_stalk_min A hrk X toBase A₀ ι hι ϖ₀ hϖ₀ halg X₀ toBase₀ iso hiso
      y hy hyc ((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base y) rfl w hw e he
      A₁ ι₁' ι₁ hι₁ hcomp ϖ₁ hϖ₁ X₁ f₁ g₁ hsq e₁ he₁ he₁'

  haveI hN₁ : IsNoetherianRing (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y)) := hnoeth₁

  have hϖ₀0 : ϖ₀ ≠ 0 := by
    intro h
    apply IsDiscreteValuationRing.not_a_field A₀
    rw [hϖ₀, h, Ideal.span_singleton_eq_bot]
  have hϖ₀irr : Irreducible ϖ₀ := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal ϖ₀ hϖ₀0 hϖ₀
  have hϖ₁0 : ϖ₁ ≠ 0 := by
    intro h
    apply IsDiscreteValuationRing.not_a_field A₁
    rw [hϖ₁, h, Ideal.span_singleton_eq_bot]
  have hϖ₁irr : Irreducible ϖ₁ := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal ϖ₁ hϖ₁0 hϖ₁
  obtain ⟨instD0, instDVR0, instC0, hirr0, -, -⟩ :=
    IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete A₀ ϖ₀ hϖ₀irr
  obtain ⟨instD1, instDVR1, instC1, hirr1, hjinj1, hjsur1⟩ :=
    IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete A₁ ϖ₁ hϖ₁irr

  let z : X₀ := (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base y
  let c₀ : A₀ →+* X₀.presheaf.stalk z :=
    (X₀.presheaf.germ ⊤ z trivial).hom.comp (toBase₀.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom)
  let c₁ : A₁ →+* X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y) :=
    (X₁.presheaf.germ ⊤ ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y) trivial).hom.comp (f₁.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom)

  let σ : AdicCompletion (maximalIdeal A₀) A₀ →+* AdicCompletion (maximalIdeal (X₀.presheaf.stalk z)) (X₀.presheaf.stalk z) :=
    e.symm.toRingHom.comp (constHom ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w))
  have hconst : ∀ o, e (σ o) = const ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w) o :=
    fun o => e.apply_symm_apply _
  have hσπ : σ (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) =
      algebraMap (X₀.presheaf.stalk z) (AdicCompletion (maximalIdeal (X₀.presheaf.stalk z)) (X₀.presheaf.stalk z)) (c₀ ϖ₀) := by
    apply e.injective
    rw [hconst]
    exact (he ϖ₀).symm

  let sc : X₀.presheaf.stalk z ≅ X₀.presheaf.stalk (g₁.base ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y)) :=
    X₀.presheaf.stalkCongr (Inseparable.of_eq hg₁y.symm)
  let fN : X₀.presheaf.stalk z →+* X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y) := (g₁.stalkMap ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y)).hom.comp sc.hom.hom
  haveI : IsLocalHom fN := RingHom.isLocalHom_comp _ _

  have hf₁y : f₁.base ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y) = closedPoint A₁ := by
    have h1 : ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))) ≫ f₁).base y = (toBase ≫ Spec.map (CommRingCat.ofHom ι₁)).base y := by
      rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, he₁]
    change f₁.base ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y) = _
    rw [← Scheme.Hom.comp_apply, h1, Scheme.Hom.comp_apply, hy]
    exact Spec_closedPoint (f := CommRingCat.ofHom ι₁)
  have hfc : ∀ a : A₀, fN (c₀ a) = c₁ (ι₁' a) := by
    intro a
    change (g₁.stalkMap ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y)).hom (sc.hom.hom ((X₀.presheaf.germ ⊤ z trivial).hom
      (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))) =
      (X₁.presheaf.germ ⊤ ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y) trivial).hom (f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom (ι₁' a)))
    have h1 : sc.hom.hom ((X₀.presheaf.germ ⊤ z trivial).hom
        (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a))) =
        (X₀.presheaf.germ ⊤ (g₁.base ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y)) trivial).hom
          (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)) := by
      change (X₀.presheaf.germ ⊤ z trivial ≫ X₀.presheaf.stalkSpecializes (Inseparable.of_eq hg₁y.symm).ge).hom _ = _
      rw [TopCat.Presheaf.germ_stalkSpecializes]
    rw [h1, Scheme.Hom.germ_stalkMap_apply]
    have h2 : g₁.app ⊤ (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)) =
        f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom (ι₁' a)) := by
      change ((toBase₀.appTop ≫ g₁.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)) = _
      rw [← Scheme.Hom.comp_appTop, hsq.w, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      congr 1
      change ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv ≫ (Spec.map (CommRingCat.ofHom ι₁')).appTop).hom a =
        ((CommRingCat.ofHom ι₁') ≫ (Scheme.ΓSpecIso (CommRingCat.of A₁)).inv).hom a
      rw [Scheme.ΓSpecIso_inv_naturality]
    exact congrArg _ h2
  have hϖe : ∃ v' : X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y), IsUnit v' ∧ fN (c₀ ϖ₀) = v' * c₁ ϖ₁ ^ e' :=
    ⟨vv, hvv, by rw [hfc]; exact hvve⟩
  have hres' : ∀ g : X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y), ∃ o : A₁, ¬ IsUnit (g - c₁ o) := hres₁
  have hgen' : maximalIdeal (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y)) ≤
      (maximalIdeal (X₀.presheaf.stalk z)).map fN ⊔ Ideal.span {c₁ ϖ₁} := by
    refine hmgen₁.trans (sup_le_sup_right ?_ _)
    rw [show fN = (g₁.stalkMap ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y)).hom.comp sc.hom.hom from rfl, ← Ideal.map_map]
    apply Ideal.map_mono
    intro m hm
    have : m = sc.hom.hom (sc.inv.hom m) := by
      rw [← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl
    rw [this]
    apply Ideal.mem_map_of_mem
    exact map_nonunit sc.inv.hom m hm
  obtain ⟨σ', ι', -, -⟩ :=
    IsLocalRing.exists_ringEquiv_adicCompletion_uvCrossingModel_of_isLocalHom_of_layer
      (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) hirr0 σ (c₀ ϖ₀) hσπ w hw e hconst
      fN c₁ ϖ₁ e' hϖe hres' hgen' hdim₁
      (algebraMap A₁ (AdicCompletion (maximalIdeal A₁) A₁) ϖ₁) hirr1
      (algebraMap A₁ (AdicCompletion (maximalIdeal A₁) A₁)) rfl hjinj1 hjsur1

  have he'0 : e' ≠ 0 := by
    intro h0
    rw [h0, pow_zero, mul_one] at hvve
    have hu : IsUnit ((X₁.presheaf.germ ⊤ ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y) trivial).hom
        (f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom (ι₁' ϖ₀)))) := by rw [hvve]; exact hvv
    have := (M3aGlue.isUnit_germ_appTop_iff f₁ ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y) (ι₁' ϖ₀)).1 hu
    apply this
    rw [hf₁y]
    exact map_nonunit ι₁' ϖ₀ (hϖ₀irr.not_isUnit)
  have h1ew : 1 ≤ e' * w := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero he'0 (by omega))
  obtain ⟨hDc, hLc, hICc⟩ := ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow
    (algebraMap A₁ (AdicCompletion (maximalIdeal A₁) A₁) ϖ₁) hirr1 (e' * w) h1ew
  haveI hlocι' : IsLocalHom ι'.toRingHom := ⟨fun a ha => by
    have := ha.map ι'.symm.toRingHom
    rwa [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.symm_apply_apply] at this⟩
  obtain ⟨hDhat, hIChat⟩ := IsIntegrallyClosed.isDomain_and_isIntegrallyClosed_of_flat_of_isLocalHom
    ι'.toRingHom (RingHom.Flat.of_bijective ι'.bijective)
  haveI hlocc : IsLocalHom (algebraMap (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y))
      (AdicCompletion (maximalIdeal (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y))) (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y)))) :=
    ⟨fun a ha => AdicCompletion.isUnit_of_isUnit_algebraMap ha⟩
  obtain ⟨-, hIC₁⟩ := IsIntegrallyClosed.isDomain_and_isIntegrallyClosed_of_flat_of_isLocalHom
    (algebraMap (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y))
      (AdicCompletion (maximalIdeal (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y))) (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y))))
    (RingHom.flat_algebraMap_iff.mpr inferInstance)

  let θ : X₁.functionField →+* X.functionField :=
    ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap (genericPoint X)).hom.comp (X₁.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom
  letI algK : Algebra X₁.functionField X.functionField := θ.toAlgebra
  letI algN : Algebra (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y)) X.functionField :=
    (θ.comp (algebraMap (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y)) X₁.functionField)).toAlgebra
  haveI : IsScalarTower (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y)) X₁.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq (fun r => rfl)
  let πy : X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y) →+* X.presheaf.stalk y := ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap y).hom
  haveI : Flat (e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))) := hflat
  have hπyflat : πy.Flat := AlgebraicGeometry.Flat.stalkMap (e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))) y
  have hXgen : genericPoint X ⤳ y := (genericPoint_spec X).specializes trivial
  have hcomm : ∀ r, algebraMap (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y)) X.functionField r =
      algebraMap (X.presheaf.stalk y) X.functionField (πy r) := by
    intro r
    change ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap (genericPoint X)).hom ((X₁.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom
      ((X₁.presheaf.stalkSpecializes ((genericPoint_spec X₁).specializes (Set.mem_univ _))).hom r)) =
      (X.presheaf.stalkSpecializes hXgen).hom (((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap y).hom r)
    rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply (e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))) (genericPoint X) y hXgen r]
    congr 1
    change (X₁.presheaf.stalkSpecializes ((genericPoint_spec X₁).specializes (Set.mem_univ _)) ≫
      X₁.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom r = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]
  have hu0 : t = θ (u 0) := by have h__af := hu 0; simp [fam] at h__af; exact h__af
  have hcoeff : ∀ i : ℕ, algebraMap (X.presheaf.stalk y) X.functionField (q.coeff i) ∈
      (algebraMap X₁.functionField X.functionField).range := by
    intro i
    by_cases hi : i ≤ d
    · refine ⟨u ⟨i + 1, by omega⟩, ?_⟩
      have := hu ⟨i + 1, by omega⟩
      simp only [fam] at this
      rw [Fin.cases_succ'] at this
      exact this.symm
    · have : q.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [this, map_zero]; exact ⟨0, map_zero _⟩
  obtain ⟨p, hp, hpq⟩ := M3aGlue.exists_map_eq_of_forall_coeff_mem_range πy hπyflat hcomm q hq hcoeff
  have hroot : Polynomial.eval₂ (algebraMap (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y)) X.functionField)
      (algebraMap X₁.functionField X.functionField (u 0)) p = 0 := by
    have halg : algebraMap (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base y)) X.functionField =
        (algebraMap (X.presheaf.stalk y) X.functionField).comp πy := RingHom.ext hcomm
    rw [halg, ← Polynomial.eval₂_map, hpq]
    change Polynomial.eval₂ _ (θ (u 0)) q = 0
    rw [← hu0]; exact hqt
  obtain ⟨r₁, hr₁⟩ := M3aGlue.mem_range_of_isIntegrallyClosed_level πy (fun r => (hcomm r).symm) hIC₁ p hp (u 0) hroot
  exact ⟨πy r₁, by rw [hr₁]; change θ (u 0) = t; exact hu0.symm⟩

end MainNL

end S_AlgebraicGeometry_isIntegrallyClosed_stalk_pullback_of_ringEquiv_adicCompletion_stalk_of_isDiscreteValuationRing
end P2MW
export P2MW.S_AlgebraicGeometry_isIntegrallyClosed_stalk_pullback_of_ringEquiv_adicCompletion_stalk_of_isDiscreteValuationRing (solution)
