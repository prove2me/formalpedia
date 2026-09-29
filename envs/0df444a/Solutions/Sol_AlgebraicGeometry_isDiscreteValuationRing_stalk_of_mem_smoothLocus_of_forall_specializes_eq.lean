-- Prove2me | solution 1 for AlgebraicGeometry.isDiscreteValuationRing_stalk_of_mem_smoothLocus_of_forall_specializes_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/5b80eb6f-b071-539b-a45d-1adbdd880b12

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specializes_isLocalization_atPrime_stalk
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isDiscreteValuationRing_stalk_of_mem_smoothLocus_of_forall_specializes_eq

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry TensorProduct

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

namespace GD0

theorem smooth_fibre {A : Type} [CommRing A] (𝔪 : Ideal A) [h𝔪 : 𝔪.IsMaximal]
    {C : Type} [CommRing C] [Algebra A C] [Algebra.Smooth A C] :
    letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    Algebra.Smooth (A ⧸ 𝔪) (C ⧸ 𝔪.map (algebraMap A C)) := by
  letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  let e1 : (A ⧸ 𝔪) ⊗[A] C ≃+* C ⧸ 𝔪.map (algebraMap A C) :=
    (Algebra.TensorProduct.comm A (A ⧸ 𝔪) C).toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C 𝔪).symm.toRingEquiv
  have he1 : ∀ t : A ⧸ 𝔪, e1 (algebraMap (A ⧸ 𝔪) ((A ⧸ 𝔪) ⊗[A] C) t) = algebraMap (A ⧸ 𝔪) (C ⧸ 𝔪.map (algebraMap A C)) t := by
    intro t
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
    show ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot C 𝔪).symm
      ((Algebra.TensorProduct.comm A (A ⧸ 𝔪) C) (Ideal.Quotient.mk 𝔪 a ⊗ₜ[A] (1 : C)))) = _
    rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul, Algebra.smul_def, mul_one]
    rfl
  exact Algebra.Smooth.of_equiv (AlgEquiv.ofRingEquiv (f := e1) he1)

end GD0

section MainGD0

open M3aGlue

theorem solution
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (η₀ : X₀) (hη₀ : toBase₀.base η₀ = closedPoint A₀) (hsm : η₀ ∈ toBase₀.smoothLocus)
    (hgen : ∀ ζ : X₀, ζ ⤳ η₀ → toBase₀.base ζ = closedPoint A₀ → ζ = η₀) :
    IsDiscreteValuationRing (X₀.presheaf.stalk η₀) ∧
      maximalIdeal (X₀.presheaf.stalk η₀) =
        Ideal.span {(X₀.presheaf.germ ⊤ η₀ trivial).hom (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom ϖ₀))} := by
  classical

  have hϖ₀0 : ϖ₀ ≠ 0 := by
    intro h; apply IsDiscreteValuationRing.not_a_field A₀; rw [hϖ₀, h, Ideal.span_singleton_eq_bot]
  have hϖ₀m : ϖ₀ ∈ maximalIdeal A₀ := by rw [hϖ₀]; exact Ideal.mem_span_singleton_self ϖ₀
  let cst : ∀ z : X₀, A₀ → X₀.presheaf.stalk z := fun z a =>
    (X₀.presheaf.germ ⊤ z trivial).hom (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv a))
  have hcstU : ∀ (z : X₀) (a : A₀), IsUnit (cst z a) ↔ a ∉ (toBase₀.base z).asIdeal := fun z a =>
    isUnit_germ_appTop_iff toBase₀ z a

  obtain ⟨U, hUaff, V, hV, hVU, hηV, hsmooth⟩ :=
    exists_smooth_of_formallySmooth_stalk toBase₀ η₀ (Scheme.Hom.mem_smoothLocus.1 hsm)
  have hUtop : U = ⊤ := by
    apply eq_top_iff.2
    intro p _
    have hxU : toBase₀.base η₀ ∈ U := hVU hηV
    rw [hη₀] at hxU
    have hsp : p ⤳ closedPoint A₀ :=
      (PrimeSpectrum.le_iff_specializes p (closedPoint A₀)).1 (IsLocalRing.le_maximalIdeal p.isPrime.ne_top)
    exact hsp.mem_open U.2 hxU
  subst hUtop
  let C : Type := Γ(X₀, V)
  let fAC : A₀ →+* C := (toBase₀.appLE ⊤ V hVU).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom
  letI algAC : Algebra A₀ C := fAC.toAlgebra
  have hsmAC : fAC.Smooth :=
    RingHom.Smooth.comp (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of A₀)).symm.commRingCatIsoToRingEquiv.bijective) hsmooth
  haveI : Algebra.Smooth A₀ C := hsmAC
  haveI : Algebra.FinitePresentation A₀ C := Algebra.Smooth.finitePresentation
  haveI : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A₀ C

  let B : Type := X₀.presheaf.stalk η₀
  letI algCB : Algebra C B := (X₀.presheaf.germ V η₀ hηV).hom.toAlgebra
  let 𝔭 : Ideal C := (hV.primeIdealOf ⟨η₀, hηV⟩).asIdeal
  haveI hlocB : IsLocalization.AtPrime B 𝔭 := hV.isLocalization_stalk ⟨η₀, hηV⟩
  haveI : IsNoetherianRing B := IsLocalization.isNoetherianRing 𝔭.primeCompl B inferInstance
  letI algAB : Algebra A₀ B := ((algebraMap C B).comp fAC).toAlgebra
  haveI : IsScalarTower A₀ C B := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  have hcV : ∀ a : A₀, algebraMap A₀ B a = cst η₀ a := fun a => by
    change (X₀.presheaf.germ V η₀ hηV).hom ((X₀.presheaf.map (homOfLE hVU).op).hom
      (toBase₀.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv a))) = _
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]
    rfl

  have hflatAC : Module.Flat A₀ C := by
    have h1 : (toBase₀.appLE ⊤ V hVU).hom.Flat :=
      HasRingHomProperty.appLE @Flat toBase₀ inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ hVU
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom.Flat :=
      RingHom.Flat.of_bijective (Scheme.ΓSpecIso (CommRingCat.of A₀)).symm.commRingCatIsoToRingEquiv.bijective
    exact h2.comp h1
  have htors : Submodule.torsion A₀ C = ⊥ := (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).1 hflatAC
  have hϖB : cst η₀ ϖ₀ ≠ 0 := by
    rw [← hcV]
    change algebraMap C B (fAC ϖ₀) ≠ 0
    intro h0
    obtain ⟨⟨s, hs⟩, hs0⟩ := (IsLocalization.map_eq_zero_iff 𝔭.primeCompl B (fAC ϖ₀)).1 h0
    have hst : (s : C) ∈ Submodule.torsion A₀ C := by
      refine ⟨⟨ϖ₀, mem_nonZeroDivisors_of_ne_zero hϖ₀0⟩, ?_⟩
      change ϖ₀ • s = 0
      rw [Algebra.smul_def, mul_comm]; exact hs0
    rw [htors] at hst
    exact hs ((Submodule.mem_bot A₀).1 hst ▸ Submodule.zero_mem 𝔭)

  have hPrimes : ∀ P : Ideal B, P.IsPrime → cst η₀ ϖ₀ ∈ P → P = maximalIdeal B := by
    intro P hP hϖP
    haveI := hP
    obtain ⟨ζ, hζ, hloc⟩ := AlgebraicGeometry.Scheme.exists_specializes_isLocalization_atPrime_stalk η₀ P
    have hPeq : (maximalIdeal (X₀.presheaf.stalk ζ)).comap (X₀.presheaf.stalkSpecializes hζ).hom = P := by
      letI instAlg : Algebra B (X₀.presheaf.stalk ζ) := (X₀.presheaf.stalkSpecializes hζ).hom.toAlgebra
      haveI : IsLocalization.AtPrime (X₀.presheaf.stalk ζ) P := hloc
      exact IsLocalization.AtPrime.under_maximalIdeal (X₀.presheaf.stalk ζ) P
    have h2 : (X₀.presheaf.stalkSpecializes hζ).hom (cst η₀ ϖ₀) = cst ζ ϖ₀ := by
      change (X₀.presheaf.germ ⊤ η₀ trivial ≫ X₀.presheaf.stalkSpecializes hζ).hom _ = _
      rw [TopCat.Presheaf.germ_stalkSpecializes]
    have hζsp : toBase₀.base ζ = closedPoint A₀ := by
      have h1 : cst ζ ϖ₀ ∈ maximalIdeal (X₀.presheaf.stalk ζ) := by
        rw [← h2, ← Ideal.mem_comap, hPeq]; exact hϖP
      have h3 : ϖ₀ ∈ (toBase₀.base ζ).asIdeal := by
        by_contra hn; exact h1 ((hcstU ζ ϖ₀).2 hn)
      apply PrimeSpectrum.ext
      exact IsLocalRing.eq_maximalIdeal
        (Ideal.IsPrime.isMaximal (toBase₀.base ζ).isPrime (fun h0 => hϖ₀0 (by rw [h0] at h3; exact h3)))
    have hζη : ζ = η₀ := hgen ζ hζ hζsp
    have key : ∀ (ζ' : X₀) (hζ' : ζ' ⤳ η₀), ζ' = η₀ →
        (maximalIdeal (X₀.presheaf.stalk ζ')).comap (X₀.presheaf.stalkSpecializes hζ').hom = maximalIdeal B := by
      rintro ζ' hζ' rfl
      rw [TopCat.Presheaf.stalkSpecializes_refl]
      exact Ideal.comap_id _
    rw [← hPeq, key ζ hζ hζη]

  set I : Ideal C := (maximalIdeal A₀).map (algebraMap A₀ C) with hIdef
  set J : Ideal B := I.map (algebraMap C B) with hJdef
  have hJ : J = Ideal.span {cst η₀ ϖ₀} := by
    rw [hJdef, hIdef, Ideal.map_map, ← IsScalarTower.algebraMap_eq, hϖ₀, Ideal.map_span, Set.image_singleton, hcV]

  letI : Field (A₀ ⧸ maximalIdeal A₀) := Ideal.Quotient.field _
  haveI hsmI : Algebra.Smooth (A₀ ⧸ maximalIdeal A₀) (C ⧸ I) := GD0.smooth_fibre (maximalIdeal A₀)
  haveI : _root_.IsReduced (C ⧸ I) := by
    have hs : (CommRingCat.ofHom (algebraMap (A₀ ⧸ maximalIdeal A₀) (C ⧸ I))).hom.Smooth :=
      RingHom.smooth_algebraMap.2 hsmI
    haveI : Smooth (Spec.map (CommRingCat.ofHom (algebraMap (A₀ ⧸ maximalIdeal A₀) (C ⧸ I)))) :=
      (HasRingHomProperty.Spec_iff (P := @Smooth)).2 hs
    have := AlgebraicGeometry.isReduced_of_smooth_of_field
      (Spec.map (CommRingCat.ofHom (algebraMap (A₀ ⧸ maximalIdeal A₀) (C ⧸ I))))
    exact (affine_isReduced_iff _).1 this
  haveI hlocQ : IsLocalization (Algebra.algebraMapSubmonoid (C ⧸ I) 𝔭.primeCompl) (B ⧸ J) := inferInstance
  haveI : _root_.IsReduced (B ⧸ J) :=
    isReduced_localizationPreserves (Algebra.algebraMapSubmonoid (C ⧸ I) 𝔭.primeCompl) (B ⧸ J) inferInstance

  have hJle : J ≤ maximalIdeal B := by
    rw [hJ, Ideal.span_le, Set.singleton_subset_iff]
    exact (IsLocalRing.mem_maximalIdeal _).2 (fun hu => (hcstU η₀ ϖ₀).1 hu (by rw [hη₀]; exact hϖ₀m))
  have hJne : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal B).ne_top (top_le_iff.1 (h ▸ hJle))
  haveI : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJne
  haveI : IsLocalRing (B ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk J) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hmax0 : maximalIdeal (B ⧸ J) = ⊥ := by
    refine le_bot_iff.1 fun x hx => ?_
    rw [Ideal.mem_bot]
    have hnil : IsNilpotent x := by
      rw [nilpotent_iff_mem_prime]
      intro Q hQ
      haveI := hQ
      have hQ' : (Q.comap (Ideal.Quotient.mk J)) = maximalIdeal B := by
        apply hPrimes _ (Ideal.comap_isPrime _ Q)
        rw [Ideal.mem_comap]
        have : Ideal.Quotient.mk J (cst η₀ ϖ₀) = 0 :=
          (Ideal.Quotient.eq_zero_iff_mem).2 (by rw [hJ]; exact Ideal.mem_span_singleton_self _)
        rw [this]; exact Q.zero_mem
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hb : b ∈ maximalIdeal B := by
        refine (IsLocalRing.mem_maximalIdeal _).2 fun hu => ?_
        exact (IsLocalRing.mem_maximalIdeal _).1 hx (hu.map _)
      rw [← hQ'] at hb
      exact hb
    exact hnil.eq_zero
  have hfield : IsField (B ⧸ J) := (IsLocalRing.isField_iff_maximalIdeal_eq).2 hmax0
  have hJmax : J = maximalIdeal B := IsLocalRing.eq_maximalIdeal (Ideal.Quotient.maximal_of_isField J hfield)

  have h𝔪 : maximalIdeal B = Ideal.span {cst η₀ ϖ₀} := by rw [← hJmax, hJ]
  have hnf : ¬ IsField B := by
    intro h
    have := (IsLocalRing.isField_iff_maximalIdeal_eq).1 h
    rw [h𝔪, Ideal.span_singleton_eq_bot] at this
    exact hϖB this
  refine ⟨((IsDiscreteValuationRing.TFAE B hnf).out 0 4).2 (by rw [h𝔪]; infer_instance), h𝔪⟩

end MainGD0

end S_AlgebraicGeometry_isDiscreteValuationRing_stalk_of_mem_smoothLocus_of_forall_specializes_eq
end P2MW
export P2MW.S_AlgebraicGeometry_isDiscreteValuationRing_stalk_of_mem_smoothLocus_of_forall_specializes_eq (solution)
