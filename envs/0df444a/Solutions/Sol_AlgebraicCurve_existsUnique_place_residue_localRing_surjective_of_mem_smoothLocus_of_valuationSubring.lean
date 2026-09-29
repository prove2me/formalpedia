-- Prove2me | solution 1 for AlgebraicCurve.existsUnique_place_residue_localRing_surjective_of_mem_smoothLocus_of_valuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/64ef272c-df86-5d69-a9d0-f171cb4ce8a4

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_KwSmoothIrredRelDimConstantEngine
import Definitions.Def_SmoothOfClosedPoints
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_fromSpecStalk_specializes_and_mem_iff_residue_eq_zero_and_eq_genericPoint_iff
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_smoothOfRelativeDimension_of_preconnectedSpace
import Theorems.Thm_AlgebraicCurve_SemistableModel_finrank_kaehlerDifferential_eq_of_smoothOfRelativeDimension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_existsUnique_place_residue_localRing_surjective_of_mem_smoothLocus_of_valuationSubring

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry TensorProduct

universe u

namespace K1

theorem localRing_le_of_specializes {F : Type} [Field F] (X : Scheme.{0}) [IsIntegral X]
    (φ : F ≃+* X.functionField) {x y : X} (h : y ⤳ x) :
    SemistableModel.localRing X φ x ≤ SemistableModel.localRing X φ y := by
  rintro f ⟨s, rfl⟩
  refine ⟨(X.presheaf.stalkSpecializes h).hom s, ?_⟩
  simp only [RingHom.coe_comp, Function.comp_apply]
  congr 1
  change (X.presheaf.stalkSpecializes h ≫ X.presheaf.stalkSpecializes _).hom s =
    (X.presheaf.stalkSpecializes _).hom s
  rw [TopCat.Presheaf.stalkSpecializes_comp]

theorem exists_div_of_stalkSpecializes {X : Scheme.{u}} [IsIntegral X] {x η : X} (h : η ⤳ x)
    (r : X.presheaf.stalk η) :
    ∃ b c : X.presheaf.stalk x, IsUnit ((X.presheaf.stalkSpecializes h).hom c) ∧
      r * (X.presheaf.stalkSpecializes h).hom c = (X.presheaf.stalkSpecializes h).hom b := by
  classical
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have hxU : x ∈ U := X.affineCover.covers x
  have hηU : η ∈ U := h.mem_open U.isOpen hxU
  letI algη : Algebra Γ(X, U) (X.presheaf.stalk η) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨η, hηU⟩
  haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk η) (hU.primeIdealOf ⟨η, hηU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨η, hηU⟩
  obtain ⟨⟨b, m⟩, hbm⟩ := IsLocalization.surj (hU.primeIdealOf ⟨η, hηU⟩).asIdeal.primeCompl r
  have hgermη : ∀ s : Γ(X, U), algebraMap Γ(X, U) (X.presheaf.stalk η) s = (X.presheaf.germ U η hηU).hom s :=
    fun s => rfl
  have hsp : ∀ s : Γ(X, U), (X.presheaf.stalkSpecializes h).hom ((X.presheaf.germ U x hxU).hom s) =
      (X.presheaf.germ U η hηU).hom s := fun s => by
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  refine ⟨(X.presheaf.germ U x hxU).hom b, (X.presheaf.germ U x hxU).hom m, ?_, ?_⟩
  · rw [hsp, ← hgermη]
    exact IsLocalization.map_units (X.presheaf.stalk η) m
  · rw [hsp, hsp, ← hgermη, ← hgermη]
    exact hbm

theorem exists_mem_maximalIdeal_isUnit_stalkSpecializes {X : Scheme.{u}} [IsIntegral X]
    {x η : X} (h : η ⤳ x) (hne : η ≠ x) :
    ∃ b ∈ maximalIdeal (X.presheaf.stalk x), IsUnit ((X.presheaf.stalkSpecializes h).hom b) := by
  classical
  have hmem : η ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact h
  obtain ⟨𝔮, rfl⟩ := hmem
  have hq : 𝔮.asIdeal ≠ maximalIdeal (X.presheaf.stalk x) := by
    intro hq
    apply hne
    have : 𝔮 = closedPoint (X.presheaf.stalk x) := PrimeSpectrum.ext hq
    rw [this, Scheme.fromSpecStalk_closedPoint]
  have hle : 𝔮.asIdeal ≤ maximalIdeal (X.presheaf.stalk x) := IsLocalRing.le_maximalIdeal_of_isPrime 𝔮.asIdeal
  obtain ⟨b, hbm, hbq⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hq)
  obtain ⟨hη', hiff, -⟩ :=
    AlgebraicGeometry.Scheme.exists_fromSpecStalk_specializes_and_mem_iff_residue_eq_zero_and_eq_genericPoint_iff
      x 𝔮.asIdeal
  refine ⟨b, hbm, ?_⟩
  have hres : X.residue _ ((X.presheaf.stalkSpecializes hη').hom b) ≠ 0 := fun h0 => hbq ((hiff b).mpr h0)
  have hres' : IsLocalRing.residue _ ((X.presheaf.stalkSpecializes hη').hom b) ≠ 0 := hres
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hres'

end K1

namespace K1Aux

variable {A : Type} [CommRing A] (𝔪 : Ideal A) [h𝔪 : 𝔪.IsMaximal]
  {C : Type} [CommRing C] [Algebra A C]

theorem isStandardSmoothOfRelativeDimension_fibre (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n A C] :
    letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    Algebra.IsStandardSmoothOfRelativeDimension n (A ⧸ 𝔪) (C ⧸ 𝔪.map (algebraMap A C)) := by
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
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv (n := n) (AlgEquiv.ofRingEquiv (f := e1) he1)

end K1Aux

namespace K1Aux

theorem transport {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S)
    (h : IsDomain R ∧ IsPrincipalIdealRing R ∧ ¬ IsField R) :
    IsDomain S ∧ IsPrincipalIdealRing S ∧ ¬ IsField S := by
  obtain ⟨h1, h2, h3⟩ := h
  haveI := h1; haveI := h2
  haveI : NoZeroDivisors S :=
    Function.Injective.noZeroDivisors e.symm e.symm.injective (map_zero _) (fun x y => map_mul _ x y)
  haveI : Nontrivial S := e.injective.nontrivial
  exact ⟨NoZeroDivisors.to_isDomain S, IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective,
    fun hS => h3 (MulEquiv.isField hS e.toMulEquiv)⟩

theorem core {A : Type} [CommRing A] (𝔪 : Ideal A) [h𝔪 : 𝔪.IsMaximal]
    {C : Type} [CommRing C] [Algebra A C] [Algebra.IsStandardSmoothOfRelativeDimension 1 A C]
    (𝔭 : Ideal C) [𝔭.IsMaximal] (h𝔭 : 𝔪.map (algebraMap A C) ≤ 𝔭)
    (B : Type) [CommRing B] [Algebra C B] [IsLocalization.AtPrime B 𝔭] [Algebra A B] [IsScalarTower A C B] :
    IsDomain (B ⧸ 𝔪.map (algebraMap A B)) ∧
      IsPrincipalIdealRing (B ⧸ 𝔪.map (algebraMap A B)) ∧
      ¬ IsField (B ⧸ 𝔪.map (algebraMap A B)) := by
  classical
  letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  set I : Ideal C := 𝔪.map (algebraMap A C) with hI
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 (A ⧸ 𝔪) (C ⧸ I) :=
    isStandardSmoothOfRelativeDimension_fibre 𝔪 1

  let mkI : C →+* C ⧸ I := Ideal.Quotient.mk I
  set 𝔭₀ : Ideal (C ⧸ I) := 𝔭.map mkI with h𝔭₀
  have hcomap : 𝔭₀.comap mkI = 𝔭 := by
    rw [h𝔭₀, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr h𝔭]
  haveI h𝔭₀max : 𝔭₀.IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective mkI Ideal.Quotient.mk_surjective ‹𝔭.IsMaximal› with h | h
    · exfalso
      apply ‹𝔭.IsMaximal›.ne_top
      rw [← hcomap, show 𝔭₀ = ⊤ from (by rw [h𝔭₀]; exact h), Ideal.comap_top]
    · exact h

  obtain ⟨hdom, hdvr⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.isDiscreteValuationRing_localization_atPrime
      (k := A ⧸ 𝔪) (A := C ⧸ I) 𝔭₀
  haveI := hdom
  haveI := hdvr

  let J : Ideal B := I.map (algebraMap C B)
  have hM : Algebra.algebraMapSubmonoid (C ⧸ I) 𝔭.primeCompl = 𝔭₀.primeCompl := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩ hx
      exact hs (by rw [← hcomap]; exact Ideal.mem_comap.mpr hx)
    · intro hx
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨s, fun hs => hx (Ideal.mem_map_of_mem _ hs), rfl⟩
  haveI : IsLocalization 𝔭₀.primeCompl (B ⧸ J) := hM ▸ (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid (C ⧸ I) 𝔭.primeCompl) (B ⧸ J))
  let e : Localization.AtPrime 𝔭₀ ≃ₐ[C ⧸ I] B ⧸ J :=
    IsLocalization.algEquiv 𝔭₀.primeCompl (Localization.AtPrime 𝔭₀) (B ⧸ J)
  have hJ : J = 𝔪.map (algebraMap A B) := by
    show (𝔪.map (algebraMap A C)).map (algebraMap C B) = 𝔪.map (algebraMap A B)
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have h0 : IsDomain (Localization.AtPrime 𝔭₀) ∧ IsPrincipalIdealRing (Localization.AtPrime 𝔭₀) ∧
      ¬ IsField (Localization.AtPrime 𝔭₀) :=
    ⟨hdom, inferInstance, IsDiscreteValuationRing.not_isField _⟩
  exact transport ((e.toRingEquiv).trans (Ideal.quotEquivOfEq hJ)) h0

end K1Aux

namespace K1Aux

noncomputable def fibreEquiv {A : Type} [CommRing A] (𝔪 : Ideal A) {C : Type} [CommRing C] [Algebra A C] :
    (A ⧸ 𝔪) ⊗[A] C ≃ₐ[A ⧸ 𝔪] C ⧸ 𝔪.map (algebraMap A C) :=
  AlgEquiv.ofRingEquiv
    (f := (Algebra.TensorProduct.comm A (A ⧸ 𝔪) C).toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C 𝔪).symm.toRingEquiv)
    (by
      intro t
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
      show ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot C 𝔪).symm
        ((Algebra.TensorProduct.comm A (A ⧸ 𝔪) C) (Ideal.Quotient.mk 𝔪 a ⊗ₜ[A] (1 : C)))) = _
      rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul,
        Algebra.smul_def, mul_one]
      rfl)

theorem core' {A : Type} [CommRing A] [IsLocalRing A] [IsAlgClosed (ResidueField A)]
    {C : Type} [CommRing C] [Algebra A C] (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n A C]
    (𝔭 : Ideal C) [𝔭.IsMaximal] (h𝔭 : (maximalIdeal A).map (algebraMap A C) ≤ 𝔭)
    (B : Type) [CommRing B] [Algebra C B] [IsLocalization.AtPrime B 𝔭] [Algebra A B] [IsScalarTower A C B] :
    haveI : IsLocalRing B := IsLocalization.AtPrime.isLocalRing B 𝔭
    ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B := by
  classical
  haveI hB : IsLocalRing B := IsLocalization.AtPrime.isLocalRing B 𝔭
  intro b

  let 𝔪 := maximalIdeal A
  let K := A ⧸ 𝔪
  letI : Field K := Ideal.Quotient.field 𝔪
  haveI : IsAlgClosed K := ‹IsAlgClosed (ResidueField A)›
  let I : Ideal C := 𝔪.map (algebraMap A C)
  let C₀ := C ⧸ I
  let mkI : C →+* C₀ := Ideal.Quotient.mk I

  haveI : Algebra.IsStandardSmooth A C := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  haveI : Algebra.FiniteType A C := inferInstance
  haveI : Algebra.FiniteType K C₀ := (inferInstance : Algebra.FiniteType K (K ⊗[A] C)).equiv (fibreEquiv 𝔪)

  let 𝔭₀ : Ideal C₀ := 𝔭.map mkI
  have hcomap : 𝔭₀.comap mkI = 𝔭 := by
    show (𝔭.map mkI).comap mkI = 𝔭
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr h𝔭]
  haveI h𝔭₀max : 𝔭₀.IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective mkI Ideal.Quotient.mk_surjective ‹𝔭.IsMaximal› with h | h
    · exfalso
      apply ‹𝔭.IsMaximal›.ne_top
      rw [← hcomap, show 𝔭₀ = ⊤ from h, Ideal.comap_top]
    · exact h

  letI : Field (C₀ ⧸ 𝔭₀) := Ideal.Quotient.field 𝔭₀
  have hbij := SmoothOfClosedPoints.bijective_algebraMap_quotient K 𝔭₀
  let π : C →+* C₀ ⧸ 𝔭₀ := (Ideal.Quotient.mk 𝔭₀).comp mkI
  have hkerπ : ∀ x : C, π x = 0 ↔ x ∈ 𝔭 := by
    intro x
    show Ideal.Quotient.mk 𝔭₀ (mkI x) = 0 ↔ x ∈ 𝔭
    rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hcomap]
  have hπA : ∀ a : A, π (algebraMap A C a) = algebraMap K (C₀ ⧸ 𝔭₀) (Ideal.Quotient.mk 𝔪 a) := fun a => rfl

  obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl b
  have hs : π (s : C) ≠ 0 := fun h => s.2 ((hkerπ _).mp h)
  obtain ⟨t, ht⟩ := hbij.2 (π c * (π (s : C))⁻¹)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
  refine ⟨a, ?_⟩
  have hmem : c - algebraMap A C a * (s : C) ∈ 𝔭 := by
    rw [← hkerπ, map_sub, map_mul, hπA, ht, inv_mul_cancel_right₀ hs, sub_self]
  have key : IsLocalization.mk' B c s - algebraMap A B a =
      IsLocalization.mk' B (c * ((1 : 𝔭.primeCompl) : C) - algebraMap A C a * (s : C)) (s * 1) := by
    rw [IsLocalization.mk'_sub, IsLocalization.mk'_one, IsScalarTower.algebraMap_apply A C B]
  rw [key]
  refine (IsLocalization.AtPrime.mk'_mem_maximal_iff B 𝔭 _ _).mpr ?_
  simpa using hmem

end K1Aux

namespace K1

theorem isDomain_and_isPrincipalIdealRing_quotient_map_maximalIdeal_of_isStandardSmoothOfRelativeDimension_one
    {A : Type} [CommRing A] [IsLocalRing A]
    {C : Type} [CommRing C] [Algebra A C] [Algebra.IsStandardSmoothOfRelativeDimension 1 A C]
    (𝔭 : Ideal C) [𝔭.IsMaximal] (h𝔭 : (maximalIdeal A).map (algebraMap A C) ≤ 𝔭)
    (B : Type) [CommRing B] [Algebra C B] [IsLocalization.AtPrime B 𝔭] [Algebra A B] [IsScalarTower A C B] :
    IsDomain (B ⧸ (maximalIdeal A).map (algebraMap A B)) ∧
      IsPrincipalIdealRing (B ⧸ (maximalIdeal A).map (algebraMap A B)) ∧
      ¬ IsField (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
  K1Aux.core (maximalIdeal A) 𝔭 h𝔭 B

theorem exists_sub_algebraMap_mem_maximalIdeal_of_isStandardSmoothOfRelativeDimension
    {A : Type} [CommRing A] [IsLocalRing A] [IsAlgClosed (ResidueField A)]
    {C : Type} [CommRing C] [Algebra A C] (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n A C]
    (𝔭 : Ideal C) [𝔭.IsMaximal] (h𝔭 : (maximalIdeal A).map (algebraMap A C) ≤ 𝔭)
    (B : Type) [CommRing B] [Algebra C B] [IsLocalization.AtPrime B 𝔭] [Algebra A B] [IsScalarTower A C B] :
    haveI : IsLocalRing B := IsLocalization.AtPrime.isLocalRing B 𝔭
    ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B :=
  K1Aux.core' n 𝔭 h𝔭 B

end K1

namespace K1

theorem read_const
    {L : Type} [Field L] (A : ValuationSubring L)
    {F : Type} [Field F] [Algebra L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A)) [IsIntegral X]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (V : X.Opens) (x : X) (hxV : x ∈ V) (a : ↥A) :
    (φ.symm : X.functionField ≃+* F).toRingHom.comp (algebraMap (X.presheaf.stalk x) X.functionField)
        ((X.presheaf.germ V x hxV).hom ((toBase.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom a)))
      = algebraMap L F (a : L) := by

  have hgerm : (X.presheaf.germ V x hxV).hom
      ((toBase.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom a)) =
      (X.presheaf.germ ⊤ x trivial).hom (toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom a)) := by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
    exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE le_top) x hxV _
  rw [hgerm]
  apply φ.injective
  rw [hφ]
  show φ (φ.symm ((X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)).hom
    ((X.presheaf.germ ⊤ x trivial).hom _))) = _
  rw [RingEquiv.apply_symm_apply, TopCat.Presheaf.germ_stalkSpecializes_apply]
  rfl

end K1

namespace K1

theorem exists_chart
    {L : Type} [Field L] (A : ValuationSubring L)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [LocallyOfFinitePresentation toBase]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (x : X) (hxs : x ∈ toBase.smoothLocus) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V), x ∈ V ∧
      (toBase.appLE ⊤ V le_top).hom.IsStandardSmoothOfRelativeDimension 1 := by
  classical
  set W : X.Opens := toBase.smoothLocus with hWdef

  haveI hsm : Smooth (W.ι ≫ toBase) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq, eq_top_iff]
    rintro y -
    rw [Scheme.Hom.mem_preimage]
    exact y.2

  haveI hne : Nonempty (W : Scheme.{0}) := ⟨⟨x, hxs⟩⟩
  haveI : IsIntegral (W : Scheme.{0}) := isIntegral_of_isOpenImmersion W.ι

  obtain ⟨n, hn⟩ := AlgebraicGeometry.Smooth.exists_smoothOfRelativeDimension_of_preconnectedSpace (W.ι ≫ toBase)
  haveI := hn
  have hW : ((W : X.Opens) : Set X).Nonempty := ⟨x, hxs⟩
  have hφ' : ∀ a : ↥A, φ (algebraMap L F (algebraMap (↥A) L a)) = SemistableModel.baseToFunctionField toBase a :=
    fun a => hφ a
  have hrank := (AlgebraicCurve.SemistableModel.finrank_kaehlerDifferential_eq_of_smoothOfRelativeDimension
    X toBase φ hφ' W hW n).2
  have hn1 : n = 1 := by rw [← hrank]; exact IsCurveOver.finrank_kaehler
  subst hn1

  obtain ⟨V, hV, hxV, hVn⟩ :=
    AlgebraicGeometry.KwSmoothIrredRelDimConstantEngine.kw_exists_relDim_appLE_top_of_relDim
      (X := (W : Scheme.{0})) (W.ι ≫ toBase) 1 ⟨x, hxs⟩
  refine ⟨W.ι ''ᵁ V, hV.image_of_isOpenImmersion W.ι, ⟨⟨x, hxs⟩, hxV, rfl⟩, ?_⟩
  exact AlgebraicGeometry.KwSmoothIrredRelDimConstantEngine.kw_appLE_top_opensImage hVn

end K1

namespace K1

set_option maxHeartbeats 3200000 in

theorem exists_place_eq_of_residue_image_raw
    {L F : Type} [Field L] [Field F] [Algebra L F] (A : ValuationSubring L)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (𝒪 : ValuationSubring F) (resd : ↥𝒪 →+* Fbar)
    (S : Subring F) [IsLocalRing ↥S]
    (hSR : ∀ f : ↥S, (f : F) ∈ 𝒪)
    (hAS : ∀ a : ↥A, algebraMap L F (a : L) ∈ S)
    (hcompat : ∀ (a : ↥A) (h : algebraMap L F (a : L) ∈ 𝒪),
      resd ⟨algebraMap L F (a : L), h⟩ = algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A a))
    (O : ValuationSubring Fbar) (hOtop : O ≠ ⊤) (hOpir : IsPrincipalIdealRing ↥O)
    (hO : ∀ g : Fbar, g ∈ O ↔ ∃ f : ↥S, resd ⟨(f : F), hSR f⟩ = g)
    (hloc : ∀ f : ↥S, f ∈ maximalIdeal ↥S ↔ resd ⟨(f : F), hSR f⟩ ∈ O.nonunits)
    (hrat : ∀ f : ↥S, ∃ a : ↥A, f - ⟨algebraMap L F (a : L), hAS a⟩ ∈ maximalIdeal ↥S) :
    ∃ Q : Place (ResidueField ↥A) Fbar,
      Q.toValuationSubring = O ∧
      Q.IsRational ∧
      (∀ f : ↥S, ∃ hR : (f : F) ∈ 𝒪, resd ⟨(f : F), hR⟩ ∈ Q.toValuationSubring) ∧
      (∀ g : Fbar, g ∈ Q.toValuationSubring →
        ∃ (f : F) (hf : f ∈ 𝒪), f ∈ S ∧ resd ⟨f, hf⟩ = g) ∧
      (∀ (f : ↥S) (hR : (f : F) ∈ 𝒪),
        IsUnit f ↔ Q.ord (resd ⟨(f : F), hR⟩) = 0 ∧ resd ⟨(f : F), hR⟩ ≠ 0) ∧
      (∃ (T : ↥S) (hR : (T : F) ∈ 𝒪), Q.ord (resd ⟨(T : F), hR⟩) = 1) ∧
      (∀ Q' : Place (ResidueField ↥A) Fbar,
        (∀ f : ↥S, ∃ hR : (f : F) ∈ 𝒪, resd ⟨(f : F), hR⟩ ∈ Q'.toValuationSubring) → Q' = Q) := by
  classical
  let red : ↥S → Fbar := fun f => resd ⟨(f : F), hSR f⟩
  have hred : ∀ f, red f = resd ⟨(f : F), hSR f⟩ := fun f => rfl
  let ρ₀ : ↥S →+* ↥𝒪 := (S.subtype).codRestrict 𝒪.toSubring (fun f => hSR f)
  let redH : ↥S →+* Fbar := resd.comp ρ₀
  have hredH : ∀ f, redH f = red f := fun f => rfl

  have hconstS : ∀ a : ↥A, red ⟨algebraMap L F (a : L), hAS a⟩ = algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A a) := by
    intro a
    rw [hred]
    exact hcompat a (hSR ⟨algebraMap L F (a : L), hAS a⟩)
  have hconst : ∀ z : ResidueField ↥A, algebraMap (ResidueField ↥A) Fbar z ∈ O := by
    intro z
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
    rw [hO]
    exact ⟨⟨algebraMap L F (a : L), hAS a⟩, hconstS a⟩

  obtain ⟨Q, rfl⟩ : ∃ Q : Place (ResidueField ↥A) Fbar, Q.toValuationSubring = O := ⟨⟨O, hconst, hOtop, hOpir⟩, rfl⟩
  have hredO : ∀ f : ↥S, red f ∈ Q.toValuationSubring := fun f => (hO _).mpr ⟨f, rfl⟩

  have hunitO : ∀ (g : Fbar) (hg : g ∈ Q.toValuationSubring), IsUnit (⟨g, hg⟩ : ↥Q.toValuationSubring) ↔ g ∉ Q.toValuationSubring.nonunits := by
    intro g hg
    rw [ValuationSubring.valuation_eq_one_iff, ValuationSubring.mem_nonunits_iff, not_lt]
    constructor
    · intro h; exact h.symm.le
    · intro h; exact le_antisymm (Q.toValuationSubring.valuation_le_one ⟨g, hg⟩) h
  have hunitS : ∀ f : ↥S, IsUnit f ↔ IsUnit (⟨red f, hredO f⟩ : ↥Q.toValuationSubring) := by
    intro f
    rw [hunitO, ← hloc, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥Q.toValuationSubring
  have hπ0 : ((π : ↥Q.toValuationSubring) : Fbar) ≠ 0 := fun h0 => hπ.ne_zero (Subtype.ext h0)
  have hordO : ∀ (g : Fbar) (hg : g ∈ Q.toValuationSubring), IsUnit (⟨g, hg⟩ : ↥Q.toValuationSubring) ↔ Q.ord g = 0 ∧ g ≠ 0 := by
    intro g hg
    constructor
    · intro hu
      refine ⟨?_, ?_⟩
      · have := Q.ord_coe_unit hu.unit
        rwa [IsUnit.unit_spec] at this
      · intro h0
        rw [show (⟨g, hg⟩ : ↥Q.toValuationSubring) = 0 from Subtype.ext h0] at hu
        exact not_isUnit_zero hu
    · rintro ⟨h0, hne⟩
      obtain ⟨u, hu⟩ := Q.exists_unit_mul_zpow hne hπ
      rw [h0, zpow_zero, mul_one] at hu
      have : (⟨g, hg⟩ : ↥Q.toValuationSubring) = (u : ↥Q.toValuationSubring) := Subtype.ext hu
      rw [this]; exact u.isUnit
  refine ⟨Q, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro y
    obtain ⟨g, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨f, hf⟩ := (hO (g : Fbar)).mp g.2
    obtain ⟨a, ha⟩ := hrat f
    refine ⟨IsLocalRing.residue ↥A a, ?_⟩
    have h1 : red (f - ⟨algebraMap L F (a : L), hAS a⟩) ∈ Q.toValuationSubring.nonunits := (hloc _).mp ha
    have h2 : red (f - ⟨algebraMap L F (a : L), hAS a⟩) = red f - red ⟨algebraMap L F (a : L), hAS a⟩ := by
      rw [← hredH, ← hredH, ← hredH, map_sub]
    rw [h2, hconstS] at h1
    have h3 : (g - algebraMap (ResidueField ↥A) ↥Q.toValuationSubring (IsLocalRing.residue ↥A a) : ↥Q.toValuationSubring) ∈
        maximalIdeal ↥Q.toValuationSubring := by
      rw [ValuationSubring.valuation_lt_one_iff, ← ValuationSubring.mem_nonunits_iff]
      have : ((g - algebraMap (ResidueField ↥A) ↥Q.toValuationSubring (IsLocalRing.residue ↥A a) : ↥Q.toValuationSubring) : Fbar) =
          red f - algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A a) := by
        push_cast; rw [Place.coe_algebraMap, ← hf]
      rw [this]; exact h1

    have h4 : IsLocalRing.residue ↥Q.toValuationSubring g =
        IsLocalRing.residue ↥Q.toValuationSubring (algebraMap (ResidueField ↥A) ↥Q.toValuationSubring (IsLocalRing.residue ↥A a)) := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact h3
    rw [h4]
    first
      | rfl
      | (rw [← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply])
  ·
    intro f; exact ⟨hSR f, hredO f⟩
  ·
    intro g hg
    obtain ⟨f, hf⟩ := (hO g).mp hg
    exact ⟨(f : F), hSR f, f.2, hf⟩
  ·
    intro f hR
    have : resd ⟨(f : F), hR⟩ = red f := rfl
    rw [this, hunitS, hordO]
  ·
    obtain ⟨T, hT⟩ := (hO (π : Fbar)).mp π.2
    refine ⟨T, hSR T, ?_⟩
    show Q.ord (red T) = 1
    rw [hred, hT]; exact Q.ord_coe_irreducible hπ
  ·
    intro Q' hQ'
    have hle : Q.toValuationSubring ≤ Q'.toValuationSubring := by
      intro g hg
      obtain ⟨f, hf⟩ := (hO g).mp hg
      obtain ⟨hR, hm⟩ := hQ' f
      rw [← hf]; exact hm
    apply Place.ext
    by_contra hne
    apply Q'.ne_top'
    obtain ⟨g, hgQ', hgO⟩ : ∃ g, g ∈ Q'.toValuationSubring ∧ g ∉ Q.toValuationSubring := by
      by_contra h
      push Not at h
      exact hne (le_antisymm (fun g hg => h g hg) hle)
    have hg0 : g ≠ 0 := fun h0 => hgO (h0 ▸ Q.toValuationSubring.zero_mem)
    obtain ⟨u, hu⟩ := Q.exists_unit_mul_zpow hg0 hπ
    have hordneg : Q.ord g < 0 := by
      by_contra h
      push Not at h
      apply hgO
      rw [hu]
      refine mul_mem (u : ↥Q.toValuationSubring).2 ?_
      obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
      rw [hn, zpow_natCast]; exact pow_mem π.2 n

    have hπinv : ((π : ↥Q.toValuationSubring) : Fbar)⁻¹ ∈ Q'.toValuationSubring := by
      obtain ⟨m, hm⟩ := Int.exists_eq_neg_ofNat (le_of_lt hordneg)
      have hm1 : 1 ≤ m := by omega
      set u' : Fbar := (((u⁻¹ : (↥Q.toValuationSubring)ˣ) : ↥Q.toValuationSubring) : Fbar) with hu'def
      have huinv : ((u : ↥Q.toValuationSubring) : Fbar) * u' = 1 := congrArg Subtype.val u.mul_inv
      have hgu : g * u' = ((π : ↥Q.toValuationSubring) : Fbar) ^ (-(m : ℤ)) := by
        rw [hu, hm, mul_assoc, mul_comm (((π : ↥Q.toValuationSubring) : Fbar) ^ _), ← mul_assoc, huinv, one_mul]
      have e1 : ((π : ↥Q.toValuationSubring) : Fbar)⁻¹ = g * u' * ((π : ↥Q.toValuationSubring) : Fbar) ^ (m - 1) := by
        rw [hgu, ← zpow_natCast, Nat.cast_sub hm1, Nat.cast_one, ← zpow_add₀ hπ0]
        have : (-(m : ℤ) + ((m : ℤ) - 1)) = -1 := by ring
        rw [this, zpow_neg_one]
      rw [e1]
      exact mul_mem (mul_mem hgQ' (hle ((u⁻¹ : (↥Q.toValuationSubring)ˣ) : ↥Q.toValuationSubring).2)) (pow_mem (hle π.2) _)
    refine eq_top_iff.mpr fun x _ => ?_
    rcases eq_or_ne x 0 with rfl | hx0
    · exact zero_mem _
    obtain ⟨v, hv⟩ := Q.exists_unit_mul_zpow hx0 hπ
    rw [hv]
    refine mul_mem (hle (v : ↥Q.toValuationSubring).2) ?_
    rcases le_or_gt 0 (Q.ord x) with h | h
    · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
      rw [hn, zpow_natCast]; exact pow_mem (hle π.2) n
    · obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat (le_of_lt h)
      rw [hn, zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem hπinv n

end K1

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
    (𝒪 : ValuationSubring F) (resd : ↥𝒪 →+* Fbar) (hsurj : Function.Surjective resd)
    (hker : RingHom.ker resd = maximalIdeal ↥𝒪)
    (hcompat : ∀ (a : ↥A) (h : algebraMap L F (a : L) ∈ 𝒪),
      resd ⟨algebraMap L F (a : L), h⟩ = algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A a))
    (h𝒪 : 𝒪.toSubring = SemistableModel.localRing X φ η) :
    let S : Subring F := SemistableModel.localRing X φ x
    (∀ f : ↥S, (f : F) ∈ 𝒪) ∧
    ∃ Q : Place (ResidueField ↥A) Fbar,
      Q.IsRational ∧
      (∀ f : ↥S, ∃ hR : (f : F) ∈ 𝒪, resd ⟨(f : F), hR⟩ ∈ Q.toValuationSubring) ∧
      (∀ g : Fbar, g ∈ Q.toValuationSubring →
        ∃ (f : F) (hf : f ∈ 𝒪), f ∈ S ∧ resd ⟨f, hf⟩ = g) ∧
      (∀ (f : ↥S) (hR : (f : F) ∈ 𝒪),
        IsUnit f ↔ Q.ord (resd ⟨(f : F), hR⟩) = 0 ∧ resd ⟨(f : F), hR⟩ ≠ 0) ∧
      (∃ (T : ↥S) (hR : (T : F) ∈ 𝒪), Q.ord (resd ⟨(T : F), hR⟩) = 1) ∧
      (∀ Q' : Place (ResidueField ↥A) Fbar,
        (∀ f : ↥S, ∃ hR : (f : F) ∈ 𝒪, resd ⟨(f : F), hR⟩ ∈ Q'.toValuationSubring) → Q' = Q) := by
  intro S
  classical

  have hle : SemistableModel.localRing X φ x ≤ SemistableModel.localRing X φ η :=
    K1.localRing_le_of_specializes X φ hηx
  have hSR : ∀ f : ↥S, (f : F) ∈ 𝒪 := fun f => by
    have : (f : F) ∈ 𝒪.toSubring := by rw [h𝒪]; exact hle f.2
    exact this
  have resd_ne_zero_of_isUnit : ∀ {f : ↥𝒪}, IsUnit f → resd f ≠ 0 := fun {f} hf h0 => by
    have hmem : f ∈ RingHom.ker resd := h0
    rw [hker] at hmem
    exact (IsLocalRing.mem_maximalIdeal f).mp hmem hf

  let ψ : X.presheaf.stalk x →+* F :=
    (φ.symm : X.functionField ≃+* F).toRingHom.comp (algebraMap (X.presheaf.stalk x) X.functionField)
  have hψS : ψ.range = S := rfl
  have hψinj : Function.Injective ψ :=
    (φ.symm : X.functionField ≃+* F).injective.comp (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)
  let eS : X.presheaf.stalk x ≃+* ↥S :=
    (RingEquiv.ofBijective ψ.rangeRestrict ⟨fun a b hab => hψinj (congrArg Subtype.val hab),
      ψ.rangeRestrict_surjective⟩).trans (RingEquiv.subringCongr hψS)
  have heS : ∀ b, ((eS b : ↥S) : F) = ψ b := fun b => rfl
  haveI : IsLocalRing ↥S := eS.isLocalRing
  have hψmem : ∀ b, ψ b ∈ S := fun b => ⟨b, rfl⟩
  have hψR : ∀ b, ψ b ∈ 𝒪 := fun b => hSR ⟨ψ b, hψmem b⟩

  let ψη : X.presheaf.stalk η →+* F :=
    (φ.symm : X.functionField ≃+* F).toRingHom.comp (algebraMap (X.presheaf.stalk η) X.functionField)
  have hψηR : ∀ r, ψη r ∈ 𝒪 := fun r => by
    have : ψη r ∈ 𝒪.toSubring := by rw [h𝒪]; exact ⟨r, rfl⟩
    exact this
  have hψη_sp : ∀ b, ψη ((X.presheaf.stalkSpecializes hηx).hom b) = ψ b := fun b => by
    simp only [ψ, ψη, RingHom.coe_comp, Function.comp_apply]
    congr 1
    change (X.presheaf.stalkSpecializes hηx ≫ X.presheaf.stalkSpecializes _).hom b =
      (X.presheaf.stalkSpecializes _).hom b
    rw [TopCat.Presheaf.stalkSpecializes_comp]
  have hψη_surj : ∀ r' : ↥𝒪, ∃ r, ψη r = (r' : F) := fun r' => by
    have : (r' : F) ∈ 𝒪.toSubring := r'.2
    rw [h𝒪] at this
    exact this

  let ι : X.presheaf.stalk x →+* ↥𝒪 := ψ.codRestrict 𝒪 hψR
  let ρ : X.presheaf.stalk x →+* Fbar := resd.comp ι
  have hρ : ∀ b, ρ b = resd ⟨ψ b, hψR b⟩ := fun b => rfl
  let ιη : X.presheaf.stalk η →+* ↥𝒪 := ψη.codRestrict 𝒪 hψηR
  have hιη_sp : ∀ b, ιη ((X.presheaf.stalkSpecializes hηx).hom b) = ι b := fun b =>
    Subtype.ext (hψη_sp b)
  have hρ_unit : ∀ b, IsUnit ((X.presheaf.stalkSpecializes hηx).hom b) → ρ b ≠ 0 := fun b hb => by
    have h1 : IsUnit (ι b) := by rw [← hιη_sp]; exact hb.map ιη
    exact resd_ne_zero_of_isUnit h1

  obtain ⟨V, hV, hxV, hchart⟩ := K1.exists_chart A X toBase φ hφ x hxs
  let C : Type := Γ(X, V)
  letI algAC : Algebra ↥A C :=
    ((toBase.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom).toAlgebra
  haveI hssC : Algebra.IsStandardSmoothOfRelativeDimension 1 ↥A C :=
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 1)).2 (toBase.appLE ⊤ V le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ↥A)).symm.commRingCatIsoToRingEquiv hchart
  let B : Type := X.presheaf.stalk x
  letI algCB : Algebra C B := (X.presheaf.germ V x hxV).hom.toAlgebra
  haveI hlocB : IsLocalization.AtPrime B (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := hV.isLocalization_stalk ⟨x, hxV⟩
  letI algAB : Algebra ↥A B := ((algebraMap C B).comp (algebraMap ↥A C)).toAlgebra
  haveI : IsScalarTower ↥A C B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have halgAB : ∀ a : ↥A, algebraMap ↥A B a =
      (X.presheaf.germ V x hxV).hom ((toBase.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom a)) :=
    fun _ => rfl

  have hconst : ∀ a : ↥A, ψ (algebraMap ↥A B a) = algebraMap L F (a : L) := fun a => by
    rw [halgAB]; exact K1.read_const A X toBase φ hφ V x hxV a
  have hAS : ∀ a : ↥A, algebraMap L F (a : L) ∈ S := fun a => by
    rw [← hconst]; exact hψmem _
  have hρA : ∀ a : ↥A, ρ (algebraMap ↥A B a) = algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A a) := by
    intro a
    have h' : algebraMap L F (a : L) ∈ 𝒪 := hconst a ▸ hψR _
    have e : (⟨ψ (algebraMap ↥A B a), hψR _⟩ : ↥𝒪) = ⟨algebraMap L F (a : L), h'⟩ := Subtype.ext (hconst a)
    rw [hρ, e]
    exact hcompat a h'
  have hρA0 : ∀ a ∈ maximalIdeal ↥A, ρ (algebraMap ↥A B a) = 0 := fun a ha => by
    rw [hρA, (IsLocalRing.residue_eq_zero_iff a).mpr ha, map_zero]

  haveI h𝔭max : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.IsMaximal := by
    apply hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩
    rw [← closure_subset_iff_isClosed]
    intro y hy
    exact Set.mem_singleton_iff.mpr (hxc y (specializes_iff_mem_closure.mpr hy))
  have h𝔭 : (maximalIdeal ↥A).map (algebraMap ↥A C) ≤ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, ← IsLocalization.AtPrime.to_map_mem_maximal_iff B (hV.primeIdealOf ⟨x, hxV⟩).asIdeal,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h0 := hρA0 a ha
    have h1 : IsUnit (ι (algebraMap ↥A B a)) := hu.map ι
    exact resd_ne_zero_of_isUnit h1 h0

  obtain ⟨hdom, hpir, hnf⟩ :=
    K1.isDomain_and_isPrincipalIdealRing_quotient_map_maximalIdeal_of_isStandardSmoothOfRelativeDimension_one
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal h𝔭 B
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  have hrat' := K1.exists_sub_algebraMap_mem_maximalIdeal_of_isStandardSmoothOfRelativeDimension 1
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal h𝔭 B

  let I : Ideal B := (maximalIdeal ↥A).map (algebraMap ↥A B)
  have hIρ : ∀ b ∈ I, ρ b = 0 := by
    have : I ≤ RingHom.ker ρ := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      exact hρA0 a ha
    exact fun b hb => this hb
  let ρbar : B ⧸ I →+* Fbar := Ideal.Quotient.lift I ρ hIρ
  have hρbar : ∀ b : B, ρbar (Ideal.Quotient.mk I b) = ρ b := fun b => rfl
  haveI : IsDomain (B ⧸ I) := hdom
  haveI : IsPrincipalIdealRing (B ⧸ I) := hpir
  haveI : IsLocalRing (B ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hmk𝔪 : ∀ b : B, b ∈ maximalIdeal B ↔ Ideal.Quotient.mk I b ∈ maximalIdeal (B ⧸ I) := fun b => by
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact ⟨fun h hu => h (IsLocalHom.map_nonunit _ hu), fun h hu => h (hu.map _)⟩

  have hρbar_inj : Function.Injective ρbar := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hne0
    have hprime : (RingHom.ker ρbar).IsPrime := RingHom.ker_isPrime ρbar
    have hmax : (RingHom.ker ρbar).IsMaximal := IsPrime.to_maximal_ideal (hpi := hprime) hne0
    have heq : RingHom.ker ρbar = maximalIdeal (B ⧸ I) := IsLocalRing.eq_maximalIdeal hmax
    obtain ⟨b, hb, hbu⟩ := K1.exists_mem_maximalIdeal_isUnit_stalkSpecializes hηx hne
    have : Ideal.Quotient.mk I b ∈ RingHom.ker ρbar := by rw [heq]; exact (hmk𝔪 b).mp hb
    exact hρ_unit b hbu (by rw [← hρbar]; exact this)

  have hfrac : ∀ g : Fbar, ∃ b c : B, ρ c ≠ 0 ∧ g * ρ c = ρ b := by
    intro g
    obtain ⟨r', hr'⟩ := hsurj g
    obtain ⟨r, hr⟩ := hψη_surj r'
    obtain ⟨b, c, hcu, hbc⟩ := K1.exists_div_of_stalkSpecializes hηx r
    refine ⟨b, c, hρ_unit c hcu, ?_⟩
    have h1 : ιη r * ι c = ι b := by
      rw [← hιη_sp, ← hιη_sp, ← map_mul, hbc]
    have h2 : ιη r = r' := Subtype.ext hr
    rw [← hr', ← h2]
    change resd (ιη r) * resd (ι c) = resd (ι b)
    rw [← map_mul, h1]
  haveI : ValuationRing (B ⧸ I) := inferInstance
  have hval : ∀ g : Fbar, g ∈ ρ.range ∨ g⁻¹ ∈ ρ.range := by
    intro g
    obtain ⟨b, c, hc0, hg⟩ := hfrac g
    obtain ⟨d, hd⟩ := ValuationRing.cond (Ideal.Quotient.mk I b) (Ideal.Quotient.mk I c)
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d
    rcases hd with hd | hd
    ·
      have h1 : ρ b * ρ d = ρ c := by
        have := congrArg ρbar hd
        simpa only [map_mul, hρbar] using this
      have hb0 : ρ b ≠ 0 := fun h0 => hc0 (by rw [← h1, h0, zero_mul])
      have hg0 : g ≠ 0 := fun h0 => hb0 (by rw [← hg, h0, zero_mul])
      right
      refine ⟨d, ?_⟩
      have e2 : ρ b * (ρ d * g) = ρ b * 1 := by
        calc ρ b * (ρ d * g) = g * (ρ b * ρ d) := by ring
        _ = g * ρ c := by rw [h1]
        _ = ρ b := hg
        _ = ρ b * 1 := (mul_one _).symm
      have e3 : ρ d * g = 1 := mul_left_cancel₀ hb0 e2
      exact (mul_eq_one_iff_eq_inv₀ hg0).mp e3
    ·
      have h1 : ρ c * ρ d = ρ b := by
        have := congrArg ρbar hd
        simpa only [map_mul, hρbar] using this
      left
      refine ⟨d, ?_⟩
      have : g * ρ c = ρ d * ρ c := by rw [hg, ← h1, mul_comm]
      exact (mul_right_cancel₀ hc0 this).symm
  let O : ValuationSubring Fbar := { ρ.range with mem_or_inv_mem' := hval }
  have hOmem : ∀ g : Fbar, g ∈ O ↔ ∃ b : B, ρ b = g := fun g => by
    change g ∈ ρ.range ↔ _
    exact RingHom.mem_range

  have hρO : ∀ b : B, ρ b ∈ O := fun b => (hOmem _).mpr ⟨b, rfl⟩
  let θ₀ : B →+* ↥O := ρ.codRestrict O hρO
  have hθ₀I : ∀ b ∈ I, θ₀ b = 0 := fun b hb => Subtype.ext (hIρ b hb)
  let θ : B ⧸ I →+* ↥O := Ideal.Quotient.lift I θ₀ hθ₀I
  have hθ : ∀ b : B, ((θ (Ideal.Quotient.mk I b) : ↥O) : Fbar) = ρ b := fun b => rfl
  have hθsurj : Function.Surjective θ := by
    rintro ⟨g, hg⟩
    obtain ⟨b, rfl⟩ := (hOmem g).mp hg
    exact ⟨Ideal.Quotient.mk I b, Subtype.ext (hθ b)⟩
  have hθinj : Function.Injective θ := by
    intro y₁ y₂ h
    obtain ⟨b₁, rfl⟩ := Ideal.Quotient.mk_surjective y₁
    obtain ⟨b₂, rfl⟩ := Ideal.Quotient.mk_surjective y₂
    apply hρbar_inj
    rw [hρbar, hρbar, ← hθ, ← hθ, h]
  let eO : B ⧸ I ≃+* ↥O := RingEquiv.ofBijective θ ⟨hθinj, hθsurj⟩
  have key : O ≠ ⊤ ∧ IsPrincipalIdealRing ↥O ∧
      (∀ g : Fbar, g ∈ O ↔ ∃ f : ↥S, resd ⟨(f : F), hSR f⟩ = g) ∧
      (∀ f : ↥S, f ∈ maximalIdeal ↥S ↔ resd ⟨(f : F), hSR f⟩ ∈ O.nonunits) ∧
      (∀ f : ↥S, ∃ a : ↥A, f - ⟨algebraMap L F (a : L), hAS a⟩ ∈ maximalIdeal ↥S) := by
    refine ⟨?_, IsPrincipalIdealRing.of_surjective θ hθsurj, ?_, ?_, ?_⟩
    ·
      intro htop
      apply hnf
      have hsurjF : Function.Surjective ρbar := by
        intro g
        have hg : g ∈ O := htop ▸ ValuationSubring.mem_top g
        obtain ⟨b, rfl⟩ := (hOmem g).mp hg
        exact ⟨Ideal.Quotient.mk I b, hρbar b⟩
      exact MulEquiv.isField (Field.toIsField Fbar)
        (RingEquiv.ofBijective ρbar ⟨hρbar_inj, hsurjF⟩).toMulEquiv
    ·
      intro g
      rw [hOmem]
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨eS b, rfl⟩
      · rintro ⟨f, rfl⟩
        refine ⟨eS.symm f, ?_⟩
        rw [hρ]
        congr 1
        apply Subtype.ext
        change ψ (eS.symm f) = (f : F)
        rw [← heS, RingEquiv.apply_symm_apply]
    ·
      intro f
      have hf : f = eS (eS.symm f) := (RingEquiv.apply_symm_apply eS f).symm
      have e1 : f ∈ maximalIdeal ↥S ↔ eS.symm f ∈ maximalIdeal B := by
        simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        constructor
        · intro h hu; exact h (by rw [hf]; exact hu.map eS)
        · intro h hu; exact h (by simpa using hu.map eS.symm)
      have e2 : resd ⟨(f : F), hSR f⟩ = ρ (eS.symm f) := by
        rw [hρ]; congr 1; apply Subtype.ext; change (f : F) = ψ (eS.symm f); rw [← heS, ← hf]
      rw [e1, e2, hmk𝔪, ← hθ, ValuationSubring.coe_mem_nonunits_iff]
      change _ ↔ eO (Ideal.Quotient.mk I (eS.symm f)) ∈ maximalIdeal ↥O
      simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      constructor
      · intro h hu; exact h (by simpa using hu.map eO.symm)
      · intro h hu; exact h (hu.map eO)
    ·
      intro f
      obtain ⟨a, ha⟩ := hrat' (eS.symm f)
      refine ⟨a, ?_⟩
      have h1 : eS (eS.symm f - algebraMap ↥A B a) = f - ⟨algebraMap L F (a : L), hAS a⟩ := by
        rw [map_sub, RingEquiv.apply_symm_apply]
        congr 1
        exact Subtype.ext (hconst a)
      rw [← h1]
      simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
      intro hu
      exact ha (by simpa using hu.map eS.symm)
  obtain ⟨hOtop, hOpir, hO, hloc, hrat⟩ := key
  obtain ⟨Q, -, hQ⟩ := K1.exists_place_eq_of_residue_image_raw A 𝒪 resd S hSR hAS hcompat O hOtop hOpir
    hO hloc hrat
  exact ⟨hSR, Q, hQ⟩

end S_AlgebraicCurve_existsUnique_place_residue_localRing_surjective_of_mem_smoothLocus_of_valuationSubring
end P2MW
export P2MW.S_AlgebraicCurve_existsUnique_place_residue_localRing_surjective_of_mem_smoothLocus_of_valuationSubring (solution)
