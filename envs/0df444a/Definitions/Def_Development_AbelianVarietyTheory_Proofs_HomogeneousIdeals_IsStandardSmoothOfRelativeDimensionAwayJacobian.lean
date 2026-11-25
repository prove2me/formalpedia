-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsStandardSmoothOfRelativeDimensionAwayJacobian
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsStandardSmoothOfRelativeDimensionAwayJacobian
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T06:11:43.558797+00:00
-- url     : https://prove2.me/theorems/a7e4d22f-1f9f-5997-984a-a5a439f000d7
-- title:
--   Is Standard Smooth Of Relative Dimension Away Jacobian
-- statement:
--   Definitions and structural lemmas for Is Standard Smooth Of Relative Dimension Away Jacobian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsStandardSmoothOfRelativeDimensionAwayJacobian.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_chartY_preimage_coordOpen_two
import Theorems.Thm_GlobalTheory_WeierstrassCurve_isPullback_chartY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_isPullback_chartZ
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineX
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineY
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ


set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
universe u
noncomputable section
namespace GlobalTheory
theorem isStandardSmoothOfRelativeDimension_away_jacobian {R S ι σ : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [Finite ι] [Finite σ]
    (P : Algebra.PreSubmersivePresentation R S ι σ) (T : Type*) [CommRing T] [Algebra S T]
    [Algebra R T] [IsScalarTower R S T] [IsLocalization.Away P.jacobian T] :
    Algebra.IsStandardSmoothOfRelativeDimension P.dimension R T := by
  let Q := Algebra.SubmersivePresentation.localizationAway T P.jacobian
  let P' : Algebra.SubmersivePresentation R T (Unit ⊕ ι) (Unit ⊕ σ) :=
    { __ := Q.toPreSubmersivePresentation.comp P
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.smul_def]
        exact (IsLocalization.Away.algebraMap_isUnit _).mul Q.jacobian_isUnit }
  refine P'.isStandardSmoothOfRelativeDimension ?_
  refine (Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension
    Q.toPreSubmersivePresentation P).trans ?_
  simp [Algebra.Presentation.dimension]
theorem isReduced_of_free_of_geometricallyReduced {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [_root_.IsReduced R] [Module.Free R A]
    [GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap R A)))] : _root_.IsReduced A := by
  refine ⟨fun a ha => ?_⟩
  let b := Module.Free.chooseBasis R A
  refine b.repr.injective (Finsupp.ext fun k => ?_)
  rw [map_zero, Finsupp.zero_apply]
  refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.mpr fun p hp => ?_)
  have h₁ : AlgebraicGeometry.IsReduced (pullback (Spec.map (CommRingCat.ofHom
      (algebraMap R p.ResidueField))) (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :=
    GeometricallyReduced.geometrically_isReduced _ _ _ (IsPullback.of_hasPullback _ _).flip
  have h₂ : _root_.IsReduced (TensorProduct R p.ResidueField A) :=
    (affine_isReduced_iff (.of (TensorProduct R p.ResidueField A))).mp
      (isReduced_of_isOpenImmersion (pullbackSpecIso R p.ResidueField A).inv)
  have h₃ : (1 : p.ResidueField) ⊗ₜ[R] a = 0 :=
    (ha.map (Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField))).eq_zero
  have h₄ := congrArg (fun x => (b.baseChange p.ResidueField).repr x k) h₃
  simp only [Module.Basis.baseChange_repr_tmul, map_zero, Finsupp.zero_apply,
    ← Algebra.algebraMap_eq_smul_one] at h₄
  exact Ideal.algebraMap_residueField_eq_zero.mp h₄
namespace WeierstrassCurve
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
open Polynomial in

instance free_coordinateRing : Module.Free R W.toAffine.CoordinateRing :=
  have : Module.Free R[X] W.toAffine.CoordinateRing :=
    .of_basis (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine)
  .trans (S := R[X])
instance flat_toSpec : Flat (toSpec W) :=
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat.{u})
  IsZariskiLocalAtSource.of_openCover (P := @Flat) (chartCover W).openCover fun b => by
    cases b
    · change Flat (chartZ W ≫ toSpec W)
      rw [chartZ_toSpec]
      exact Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
    · change Flat (chartY W ≫ toSpec W)
      rw [chartY_toSpec]
      exact Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
section Presentation
open MvPolynomial
variable (i : Fin 3)
def dehomRelation : Fin 2 → MvPolynomial (Fin 3) R := ![W.toProjective.polynomial, X i - 1]
abbrev DehomRing : Type u := MvPolynomial (Fin 3) R ⧸ Ideal.span (Set.range (dehomRelation W i))
def dehomCoord (j : Fin 3) : DehomRing W i := Ideal.Quotient.mk _ (X j)
@[simp] theorem dehomCoord_self : dehomCoord W i i = 1 :=
  Ideal.Quotient.eq.mpr (Ideal.subset_span ⟨1, rfl⟩)
theorem eval₂_dehomCoord (p : MvPolynomial (Fin 3) R) :
    eval₂ (algebraMap R (DehomRing W i)) (dehomCoord W i) p = Ideal.Quotient.mk _ p :=
  RingHom.congr_fun (f := eval₂Hom (algebraMap R (DehomRing W i)) (dehomCoord W i))
    (MvPolynomial.ringHom_ext (fun r => by simp; rfl) (fun i => by simp [dehomCoord])) p
theorem equation_dehomCoord :
    (W.map (algebraMap R (DehomRing W i))).toProjective.Equation (dehomCoord W i) := by
  change (W.toProjective.map _).Equation _
  rw [WeierstrassCurve.Projective.Equation, WeierstrassCurve.Projective.map_polynomial,
    MvPolynomial.eval_map, eval₂_dehomCoord, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨0, rfl⟩
theorem bijective_awayEval_dehom : Function.Bijective
    (awayEval W i (algebraMap R _) (dehomCoord W i) (equation_dehomCoord W i) (by simp)) := by
  have hm := awayEval_awayCoord_mul W i (algebraMap R _) (dehomCoord W i)
    (equation_dehomCoord W i) (by simp)
  set ℓ := awayEval W i (algebraMap R _) (dehomCoord W i) (equation_dehomCoord W i) (by simp)
  simp only [dehomCoord_self, mul_one] at hm
  have hr : ∀ r, ℓ (awayConst W i r) = algebraMap R _ r := awayEval_awayConst W i _ _ _ _
  let g : DehomRing W i →+* AwayRing W i :=
    Ideal.Quotient.lift _ (eval₂Hom (awayConst W i) (awayCoord W i)) (by
      intro a ha
      refine (show Ideal.span (Set.range (dehomRelation W i)) ≤ RingHom.ker _ from ?_) ha
      rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      fin_cases k
      · have h := equation_awayCoord W i
        change (W.toProjective.map _).Equation _ at h
        rwa [WeierstrassCurve.Projective.Equation, WeierstrassCurve.Projective.map_polynomial,
          MvPolynomial.eval_map] at h
      · simp [dehomRelation])
  have gr : ∀ r, g (algebraMap R _ r) = awayConst W i r := fun r => eval₂_C ..
  have gc : ∀ j, g (dehomCoord W i j) = awayCoord W i j := fun j => eval₂_X ..
  refine (RingEquiv.ofRingHom ℓ g ?_ ?_).bijective
  · exact Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext
      (fun r => (congrArg ℓ (gr r)).trans (hr r)) (fun j => (congrArg ℓ (gc j)).trans (hm j)))
  · exact awayRing_hom_ext W i (fun r => by simp [hr, gr]) (fun j => by simp [hm, gc])
def dehomChart : Spec (.of (DehomRing W i)) ⟶ scheme W :=
  pt W (dehomCoord W i) (.of_isUnit (equation_dehomCoord W i) i (by simp))
instance : IsOpenImmersion (dehomChart W i) :=
  isOpenImmersion_ptHom W i _ _ (.of_isUnit (equation_dehomCoord W i) i (by simp)) (by simp)
    (bijective_awayEval_dehom W i)
theorem opensRange_dehomChart : (dehomChart W i).opensRange = coordOpen W i :=
  TopologicalSpace.Opens.ext (range_ptHom W i _ _
    (.of_isUnit (equation_dehomCoord W i) i (by simp)) (by simp) (bijective_awayEval_dehom W i))
@[reassoc (attr := simp)]
theorem dehomChart_toSpec : dehomChart W i ≫ toSpec W =
    Spec.map (CommRingCat.ofHom (algebraMap R (DehomRing W i))) :=
  pt_toSpec ..
end Presentation
theorem of_dehomChart (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
    (h : ∀ i, P (Spec.map (CommRingCat.ofHom (algebraMap R (DehomRing W i))))) :
    P (toSpec W) := by
  refine IsZariskiLocalAtSource.of_openCover (P := P)
    (Scheme.Cover.mkOfCovers (Fin 3) _ (dehomChart W) fun x => ?_) fun (i : Fin 3) => ?_
  · rcases coordOpen_one_sup_coordOpen_two W |>.ge (Set.mem_univ x) with hx | hx
    · rw [← opensRange_dehomChart] at hx
      exact ⟨1, hx⟩
    · rw [← opensRange_dehomChart] at hx
      exact ⟨2, hx⟩
  · change P (dehomChart W i ≫ toSpec W)
    rw [dehomChart_toSpec]
    exact h i
instance locallyOfFinitePresentation_toSpec : LocallyOfFinitePresentation (toSpec W) :=
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation.{u})
  of_dehomChart W @LocallyOfFinitePresentation fun _ =>
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2
      (RingHom.finitePresentation_algebraMap.2
        (Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))))
section Smooth
open MvPolynomial
theorem nonsingular_of_Δ_ne_zero {F : Type*} [Field F] {V : WeierstrassCurve F} (hΔ : V.Δ ≠ 0)
    {P : Fin 3 → F} (h : V.toProjective.Equation P) {i : Fin 3} (hi : P i ≠ 0) :
    V.toProjective.Nonsingular P := by
  by_cases hz : P 2 = 0
  · have hx := WeierstrassCurve.Projective.X_eq_zero_of_Z_eq_zero h hz
    have hy : P 1 ≠ 0 := fun hy => hi <| by fin_cases i <;> assumption
    refine (WeierstrassCurve.Projective.nonsingular_of_Z_eq_zero hz).mpr ⟨h, Or.inr ?_⟩
    simpa [hx] using hy
  · exact (WeierstrassCurve.Projective.nonsingular_of_Z_ne_zero hz).mpr <|
      (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp <|
        (WeierstrassCurve.Projective.equation_of_Z_ne_zero hz).mp h
theorem span_pderiv_eq_top {A : Type*} [CommRing A] {V : WeierstrassCurve A} (hΔ : IsUnit V.Δ)
    {P : Fin 3 → A} (h : V.toProjective.Equation P) {i : Fin 3} (hi : IsUnit (P i)) :
    Ideal.span (Set.range fun j : {j : Fin 3 // j ≠ i} =>
      MvPolynomial.eval P (pderiv j.1 V.toProjective.polynomial)) = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  let := Ideal.Quotient.field m
  set g : A →+* A ⧸ m := Ideal.Quotient.mk m
  have hi' : (g ∘ P) i ≠ 0 := (hi.map g).ne_zero
  have hns : (V.map g).toProjective.Nonsingular (g ∘ P) :=
    nonsingular_of_Δ_ne_zero (by rw [WeierstrassCurve.map_Δ]; exact (hΔ.map g).ne_zero)
      (h.map g) hi'
  set D : Fin 3 → A ⧸ m := fun j =>
    MvPolynomial.eval (g ∘ P) (pderiv j (V.map g).toProjective.polynomial) with hD
  have hj : ∀ j, j ≠ i → D j = 0 := fun j hj => by
    have e : (V.map g).toProjective.polynomial = MvPolynomial.map g V.toProjective.polynomial :=
      WeierstrassCurve.Projective.map_polynomial ..
    simp only [hD]
    rw [e, pderiv_map, MvPolynomial.eval_map, ← MvPolynomial.eval₂_comp]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span ⟨⟨j, hj⟩, rfl⟩))
  have euler : 3 * _ = (g ∘ P) 0 * D 0 + (g ∘ P) 1 * D 1 + (g ∘ P) 2 * D 2 :=
    (V.map g).toProjective.polynomial_relation (g ∘ P)
  have h0 : MvPolynomial.eval (g ∘ P) (V.map g).toProjective.polynomial = 0 := hns.1
  rw [h0, mul_zero, ← Fin.sum_univ_three
    (fun j => (g ∘ P) j * D j), Finset.sum_eq_single i (fun j _ h => by rw [hj j h, mul_zero])
    (by simp)] at euler
  have hall : ∀ j, D j = 0 := fun j => by
    by_cases h : j = i
    · exact h ▸ (mul_eq_zero.mp euler.symm).resolve_left hi'
    · exact hj j h
  rcases hns.2 with h | h | h
  exacts [h (hall 0), h (hall 1), h (hall 2)]
variable {i j : Fin 3} (hij : j ≠ i)
def dehomPresentation : Algebra.PreSubmersivePresentation R (DehomRing W i) (Fin 3) (Fin 2) :=
  .naive (v := dehomRelation W i) ![j, i] (by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [hij.symm])
theorem jacobian_dehomPresentation : (dehomPresentation W hij).jacobian =
    Ideal.Quotient.mk _ (pderiv j W.toProjective.polynomial) := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_fin_two]
  have h : ∀ a b, (dehomPresentation W hij).jacobiMatrix a b =
      pderiv (![j, i] a) (dehomRelation W i b) := fun a b =>
    Algebra.PreSubmersivePresentation.jacobiMatrix_naive ..
  have h₁ : (dehomPresentation W hij).jacobiMatrix 1 1 = 1 := by
    rw [h]
    change pderiv i (X i - 1 : MvPolynomial (Fin 3) R) = (1 : MvPolynomial (Fin 3) R)
    simp
  have h₂ : (dehomPresentation W hij).jacobiMatrix 0 1 = 0 := by
    rw [h]
    change pderiv j (X i - 1 : MvPolynomial (Fin 3) R) = (0 : MvPolynomial (Fin 3) R)
    simp [hij.symm]
  rw [h₁, h₂, mul_one, zero_mul, sub_zero, h, Algebra.Generators.algebraMap_apply]
  exact eval₂_dehomCoord W i _
include hij in

theorem isStandardSmoothOfRelativeDimension_away_pderiv (T : Type*) [CommRing T]
    [Algebra (DehomRing W i) T] [Algebra R T] [IsScalarTower R (DehomRing W i) T]
    [IsLocalization.Away
      (Ideal.Quotient.mk _ (pderiv j W.toProjective.polynomial) : DehomRing W i) T] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R T := by
  have : IsLocalization.Away (dehomPresentation W hij).jacobian T := by
    rwa [jacobian_dehomPresentation]
  simpa [Algebra.Presentation.dimension] using
    isStandardSmoothOfRelativeDimension_away_jacobian (dehomPresentation W hij) T
theorem locally_isStandardSmoothOfRelativeDimension_dehomRing (hΔ : IsUnit W.Δ) (i : Fin 3) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap R (DehomRing W i)) := by
  have h := span_pderiv_eq_top (V := W.map (algebraMap R (DehomRing W i)))
    (by rw [WeierstrassCurve.map_Δ]; exact hΔ.map _) (equation_dehomCoord W i) (i := i) (by simp)
  have e : (W.map (algebraMap R (DehomRing W i))).toProjective.polynomial =
      MvPolynomial.map _ W.toProjective.polynomial :=
    WeierstrassCurve.Projective.map_polynomial ..
  simp only [e, pderiv_map, MvPolynomial.eval_map, eval₂_dehomCoord] at h
  refine ⟨_, h, ?_⟩
  rintro _ ⟨⟨j, hj⟩, rfl⟩
  rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact isStandardSmoothOfRelativeDimension_away_pderiv W hj _
theorem smoothOfRelativeDimension_toSpec_of_isUnit (hΔ : IsUnit W.Δ) :
    SmoothOfRelativeDimension 1 (toSpec W) :=
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{u} 1)
  of_dehomChart W (@SmoothOfRelativeDimension 1) fun i =>
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).2
      (locally_isStandardSmoothOfRelativeDimension_dehomRing W hΔ i)
instance smoothOfRelativeDimension_toSpec [W.IsElliptic] :
    SmoothOfRelativeDimension 1 (toSpec W) :=
  smoothOfRelativeDimension_toSpec_of_isUnit W W.isUnit_Δ
instance smooth_toSpec [W.IsElliptic] : Smooth (toSpec W) :=
  SmoothOfRelativeDimension.smooth 1 _
instance smooth_coordinateRing [W.IsElliptic] : Algebra.Smooth R W.toAffine.CoordinateRing := by
  refine RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)
    (φ := CommRingCat.ofHom (algebraMap R W.toAffine.CoordinateRing))).1 ?_)
  rw [← chartZ_toSpec]
  infer_instance
instance smooth_originRing [W.IsElliptic] : Algebra.Smooth R (OriginRing W) := by
  refine RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)
    (φ := CommRingCat.ofHom (algebraMap R (OriginRing W)))).1 ?_)
  rw [← chartY_toSpec]
  infer_instance
end Smooth
section Integral
open Polynomial
theorem originW_mem_nonZeroDivisors_originRing : originW W ∈ nonZeroDivisors (OriginRing W) := by
  have h : IsSMulRegular (OriginRing W) (X : R[X]) :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors
      (monic_X.mem_nonZeroDivisors : (X : R[X]) ∈ nonZeroDivisors R[X])
  rw [mem_nonZeroDivisors_iff_left]
  intro a ha
  refine h.right_eq_zero_of_smul ?_
  rw [Algebra.smul_def]
  exact ha
theorem exists_isOpenImmersion_away_originW :
    ∃ f : Spec (.of (Localization.Away (originW W))) ⟶ Spec (.of W.toAffine.CoordinateRing),
      IsOpenImmersion f ∧ f ≫ chartZ W =
        Spec.map (CommRingCat.ofHom (algebraMap (OriginRing W) _)) ≫ chartY W := by
  set g := Spec.map (CommRingCat.ofHom
    (algebraMap (OriginRing W) (Localization.Away (originW W)))) with hg
  have : IsOpenImmersion g := IsOpenImmersion.of_isLocalization (originW W)
  have hr : Set.range (g ≫ chartY W) ⊆ Set.range (chartZ W) := by
    rintro _ ⟨x, rfl⟩
    rw [← Scheme.Hom.coe_opensRange, opensRange_chartZ, Scheme.Hom.comp_apply]
    change g x ∈ chartY W ⁻¹ᵁ coordOpen W 2
    rw [chartY_preimage_coordOpen_two]
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away (originW W))
      (originW W)).le ⟨x, rfl⟩
  refine ⟨IsOpenImmersion.lift (chartZ W) (g ≫ chartY W) hr, ?_, IsOpenImmersion.lift_fac ..⟩
  have : IsOpenImmersion (IsOpenImmersion.lift (chartZ W) (g ≫ chartY W) hr ≫ chartZ W) := by
    rw [IsOpenImmersion.lift_fac]
    infer_instance
  exact .of_comp _ (chartZ W)
instance isDomain_originRing [IsDomain R] : IsDomain (OriginRing W) := by
  have : Nontrivial (OriginRing W) := (originAug W).toRingHom.domain_nontrivial
  have hinj : Function.Injective (algebraMap (OriginRing W) (Localization.Away (originW W))) :=
    IsLocalization.injective _ (M := Submonoid.powers (originW W))
      (Submonoid.powers_le.mpr (originW_mem_nonZeroDivisors_originRing W))
  have : Nontrivial (Localization.Away (originW W)) := hinj.nontrivial
  obtain ⟨f, hf, -⟩ := exists_isOpenImmersion_away_originW W
  have : IsIntegral (Spec (.of (Localization.Away (originW W)))) :=
    isIntegral_of_isOpenImmersion f
  have : IsDomain (Localization.Away (originW W)) :=
    (affine_isIntegral_iff (.of (Localization.Away (originW W)))).mp this
  exact hinj.isDomain _
theorem denseRange_chartZ : DenseRange (chartZ W) := by
  intro x
  rcases exists_chartY_or_chartZ W x with ⟨y, rfl⟩ | hx
  · have hd : Dense (PrimeSpectrum.basicOpen (originW W) : Set (PrimeSpectrum (OriginRing W))) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away (originW W))
        (originW W)]
      refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_
      rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsLocalization.injective _
        (M := Submonoid.powers (originW W))
        (Submonoid.powers_le.mpr (originW_mem_nonZeroDivisors_originRing W)))]
      exact bot_le
    rw [← chartY_preimage_coordOpen_two, ← opensRange_chartZ] at hd
    exact (chartY W).continuous.closure_preimage_subset _ (hd y)
  · exact subset_closure hx
instance isIntegral_scheme [IsDomain R] : IsIntegral (scheme W) := by
  have : ∀ b, IsReduced ((chartCover W).openCover.X b) := fun b => by
    cases b
    · exact inferInstanceAs (IsReduced (Spec (.of W.toAffine.CoordinateRing)))
    · exact inferInstanceAs (IsReduced (Spec (.of (OriginRing W))))
  have : IsReduced (scheme W) := .of_openCover _ (chartCover W).openCover
  have : IrreducibleSpace (scheme W) := by
    have h := ((IrreducibleSpace.isIrreducible_univ _).image (chartZ W)
      (chartZ W).continuous.continuousOn).closure
    rw [Set.image_univ, (denseRange_chartZ W).closure_range] at h
    exact (irreducibleSpace_def _).mpr h
  exact isIntegral_of_irreducibleSpace_of_isReduced _
instance geometricallyIntegral_toSpec : GeometricallyIntegral (toSpec W) :=
  ⟨geometrically_iff_of_commRing.mpr fun K _ _ _ _ _ h =>
    IsIntegral.of_isIso ((isPullback_mapHom W (algebraMap R K) rfl).isoIsPullback _ _ h).hom⟩
instance geometricallyConnected_toSpec : GeometricallyConnected (toSpec W) :=
  ⟨fun _ _ y _ fst snd h =>
    have := (geometricallyIntegral_toSpec W).1 y fst snd h
    inferInstance⟩
instance isReduced_coordinateRing [_root_.IsReduced R] : _root_.IsReduced W.toAffine.CoordinateRing :=
  have : GeometricallyReduced
      (Spec.map (CommRingCat.ofHom (algebraMap R W.toAffine.CoordinateRing))) :=
    ⟨geometrically_iff_of_commRing.mpr fun K _ _ _ _ _ h => by
      have h' := (isPullback_chartZ W (algebraMap R K) rfl).paste_vert
        (isPullback_mapHom W (algebraMap R K) rfl)
      rw [chartZ_toSpec W] at h'
      exact isReduced_of_isOpenImmersion (h.isoIsPullback _ _ h').hom⟩
  isReduced_of_free_of_geometricallyReduced (R := R)
instance isReduced_originRing [_root_.IsReduced R] : _root_.IsReduced (OriginRing W) :=
  have : GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap R (OriginRing W)))) :=
    ⟨geometrically_iff_of_commRing.mpr fun K _ _ _ _ _ h => by
      have h' := (isPullback_chartY W (algebraMap R K) rfl).paste_vert
        (isPullback_mapHom W (algebraMap R K) rfl)
      rw [chartY_toSpec W] at h'
      exact isReduced_of_isOpenImmersion (h.isoIsPullback _ _ h').hom⟩
  isReduced_of_free_of_geometricallyReduced (R := R)
instance isReduced_scheme [_root_.IsReduced R] : AlgebraicGeometry.IsReduced (scheme W) :=
  have : ∀ b, AlgebraicGeometry.IsReduced ((chartCover W).openCover.X b) := fun b => by
    cases b
    · exact inferInstanceAs (AlgebraicGeometry.IsReduced (Spec (.of W.toAffine.CoordinateRing)))
    · exact inferInstanceAs (AlgebraicGeometry.IsReduced (Spec (.of (OriginRing W))))
  .of_openCover _ (chartCover W).openCover
end Integral
example : SmoothOfRelativeDimension 1 (toSpec (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve ℚ)) :=
  smoothOfRelativeDimension_toSpec_of_isUnit _ (by
    simp only [isUnit_iff_ne_zero, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    norm_num)
end WeierstrassCurve
end GlobalTheory


