-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0038
-- name    : PNT_ZeroFree_433_0038
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T14:17:44.032315+00:00
-- url     : https://prove2.me/theorems/ad392cab-9de8-4e3a-abd0-50bc3637ec6d
-- title:
--   Zero-free region foundations: Poisson.EisensteinLattice [0038]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Poisson.EisensteinLattice
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Poisson/EisensteinLattice.lean#L350-L623

import Definitions.Def_PNT_ZeroFree_433_0038_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Poisson/EisensteinLattice.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical

namespace EisensteinSchwartzPoisson

section
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace


end

section
open scoped RealInnerProductSpace


end

section
open MeasureTheory EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace


theorem finite_phase_sum {R : Type*} [Fintype R]
    (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b : R → ℂ) (P : R → ℂ) :
    (∑ r : R, P r * (inverseJacobian A • ∑' p : ℤ × ℤ,
      Real.fourierChar (inner ℝ (b r) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) •
        (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))))) =
    inverseJacobian A • ∑' p : ℤ × ℤ,
      (∑ r : R, P r * (Real.fourierChar (inner ℝ (b r)
        (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) : ℂ)) *
        (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))) := by
  classical
  have hs (r : R) : Summable (fun p : ℤ × ℤ =>
      P r * (Real.fourierChar (inner ℝ (b r)
        (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) •
        (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))))) := by
    apply Summable.mul_left
    apply Summable.of_norm
    simpa only [Circle.norm_smul] using dual_lattice_summable_norm f A
  simp_rw [mul_smul_comm, ← tsum_mul_left]
  rw [← Finset.smul_sum, ← Summable.tsum_finsetSum (fun r _ => hs r)]
  congr 1
  apply tsum_congr
  intro p
  simp only [Circle.smul_def, smul_eq_mul, Finset.sum_mul, mul_assoc]

theorem actual_eisenstein_periodic_fourier (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          (Real.fourierChar (inner ℝ
            (eisEmbedding (GaussianShiftedPartition.representative c r))
            (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) : ℂ)) *
          (𝓕 f) (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [actual_eisenstein_periodic_poisson f c hc P]
  have h := finite_phase_sum f
    (eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc))
    (fun r => eisEmbedding (GaussianShiftedPartition.representative c r)) P
  rw [eisenstein_inverseJacobian] at h
  exact h

end

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem dualMap_trans (A B : ℂ ≃L[ℝ] ℂ) (z : ℂ) :
    dualMap (A.trans B) z = dualMap B (dualMap A z) := by
  change (ContinuousLinearMap.adjoint
    (A.symm.toContinuousLinearMap.comp B.symm.toContinuousLinearMap)) z = _
  rw [ContinuousLinearMap.adjoint_comp]
  rfl

theorem dual_basis_apply (w : ℂ) (hw : w.im ≠ 0) (z : ℂ) :
    dualMap (basisEquiv w hw) z =
      complexPoint z.re ((z.im - w.re * z.re) / w.im) := by
  apply ext_inner_left ℝ
  intro v
  rw [dualMap, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ ((basisEquiv w hw).symm v) z = _
  simp only [basisEquiv_symm_apply, Complex.inner, complexPoint,
    Complex.mul_re,  Complex.conj_re, Complex.conj_im]
  field_simp [hw]
  ring

theorem dual_mul_apply (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    dualMap (complexMulEquiv c hc) z = (starRingEnd ℂ c)⁻¹ * z := by
  apply ext_inner_left ℝ
  intro v
  rw [dualMap, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (c⁻¹ * v) z = _
  simp only [Complex.inner, map_mul, map_inv₀]
  congr 1
  ring

theorem eisensteinDualFrequency_explicit (c : ℂ) (hc : c ≠ 0) (p : ℤ × ℤ) :
    eisensteinDualFrequency c hc p =
      complexPoint (p.1 : ℝ) (((p.1 : ℝ) + 2 * (p.2 : ℝ)) / Real.sqrt 3) /
        starRingEnd ℂ c := by
  unfold eisensteinDualFrequency eisensteinLatticeMap scaledBasisEquiv
  rw [dualMap_trans, dual_basis_apply, dual_mul_apply]
  have he : complexPoint (complexPoint (p.1 : ℝ) (p.2 : ℝ)).re
      (((complexPoint (p.1 : ℝ) (p.2 : ℝ)).im - omega3.re *
        (complexPoint (p.1 : ℝ) (p.2 : ℝ)).re) / omega3.im) =
      complexPoint (p.1 : ℝ) (((p.1 : ℝ) + 2 * (p.2 : ℝ)) / Real.sqrt 3) := by
    apply Complex.ext
    · rfl
    · simp only [complexPoint, omega3_im]
      have hr : omega3.re = -(1 / 2 : ℝ) := by norm_num [omega3]
      rw [hr]
      ring
  rw [he]
  ring

def explicitDualFrequency (c : ℂ) (p : ℤ × ℤ) : ℂ :=
  complexPoint (p.1 : ℝ) (((p.1 : ℝ) + 2 * (p.2 : ℝ)) / Real.sqrt 3) /
    starRingEnd ℂ c

theorem actual_eisenstein_poisson_explicit (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          (Real.fourierChar (inner ℝ
            (eisEmbedding (GaussianShiftedPartition.representative c r))
            (explicitDualFrequency (eisEmbedding c) p)) : ℂ)) *
          (𝓕 f) (explicitDualFrequency (eisEmbedding c) p) := by
  simpa only [eisensteinDualFrequency_explicit, explicitDualFrequency] using
    actual_eisenstein_periodic_fourier f c hc P

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

def radialTest (W : 𝓢(ℝ, ℂ)) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLM ℂ (Function.hasTemperateGrowth_norm_sq ℂ)
    ⟨1, 1, fun z => by
      simp only [pow_one, one_mul, norm_pow, Real.norm_of_nonneg (norm_nonneg z)]
      nlinarith [sq_nonneg (‖z‖ - 1)]⟩ W

@[simp] theorem radialTest_apply (W : 𝓢(ℝ, ℂ)) (z : ℂ) :
    radialTest W z = W (‖z‖ ^ 2) := rfl

def compactRadialTest (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W) : 𝓢(ℂ, ℂ) :=
  radialTest (hWc.toSchwartzMap hWs)

@[simp] theorem compactRadialTest_apply (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W) (z : ℂ) :
    compactRadialTest W hWc hWs z = W (‖z‖ ^ 2) := rfl

theorem actual_radial_poisson (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * W (‖eisEmbedding z‖ ^ 2)) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          (Real.fourierChar (inner ℝ
            (eisEmbedding (GaussianShiftedPartition.representative c r))
            (explicitDualFrequency (eisEmbedding c) p)) : ℂ)) *
          (𝓕 (compactRadialTest W hWc hWs)) (explicitDualFrequency (eisEmbedding c) p) := by
  simpa only [compactRadialTest_apply] using
    actual_eisenstein_poisson_explicit (compactRadialTest W hWc hWs) c hc P

end EisensteinSchwartzPoisson

open scoped BigOperators Classical

namespace IdealGaussCRT

noncomputable def coordinateAddChar {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, CommRing (R i)]
    (e : T ≃+* ∀ i, R i) (ψ : AddChar T ℂ) (i : ι) : AddChar (R i) ℂ := by
  classical
  exact {
    toFun := fun z => ψ (e.symm (Pi.single i z))
    map_zero_eq_one' := by simp
    map_add_eq_mul' := by
      intro z w
      rw [Pi.single_add, map_add, AddChar.map_add_eq_mul] }

private theorem addChar_finite_sum {ι T : Type*} [AddCommMonoid T]
    (ψ : AddChar T ℂ) (s : Finset ι) (f : ι → T) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, AddChar.map_add_eq_mul, ih]

theorem addChar_finite_crt_factor {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, CommRing (R i)]
    (e : T ≃+* ∀ i, R i) (ψ : AddChar T ℂ) (x : T) :
    ψ x = ∏ i, coordinateAddChar R e ψ i (e x i) := by
  classical
  have hx : (∑ i, e.symm (Pi.single i (e x i))) = x := by
    rw [← map_sum, Finset.univ_sum_single, e.symm_apply_apply]
  calc
    ψ x = ψ (∑ i, e.symm (Pi.single i (e x i))) := congrArg ψ hx.symm
    _ = ∏ i, ψ (e.symm (Pi.single i (e x i))) := addChar_finite_sum ψ _ _
    _ = _ := rfl

theorem gauss_transform_finite_crt {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, Field (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i)
    (χ : ∀ i, MulChar (R i) ℂ) (ψ : AddChar T ℂ)
    (hχ : ∀ i, χ i ≠ 1) (h : T) :
    (∑ x : T, (∏ i, χ i (e x i)) * ψ (h * x)) =
      ∏ i, if e h i = 0 then 0 else
        (χ i (e h i))⁻¹ * gaussSum (χ i) (coordinateAddChar R e ψ i) := by
  classical
  calc
    (∑ x : T, (∏ i, χ i (e x i)) * ψ (h * x)) =
        ∑ x : T, ∏ i, χ i (e x i) *
          coordinateAddChar R e ψ i (e h i * e x i) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [addChar_finite_crt_factor R e ψ (h * x)]
      simp only [map_mul, Pi.mul_apply, Finset.prod_mul_distrib]
    _ = ∑ x : ∀ i, R i, ∏ i, χ i (x i) *
          coordinateAddChar R e ψ i (e h i * x i) :=
      Equiv.sum_comp e.toEquiv (fun z : ∀ i, R i =>
        ∏ i, χ i (z i) * coordinateAddChar R e ψ i (e h i * z i))
    _ = _ := ShortDraftFiniteGaussFourier.product_gauss_transform
      R χ (coordinateAddChar R e ψ) hχ (e h)

theorem gauss_transform_finite_crt_scalar {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, Field (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i)
    (χ : ∀ i, MulChar (R i) ℂ) (ψ : AddChar T ℂ)
    (hχ : ∀ i, χ i ≠ 1) (h : T) :
    (∑ x : T, (∏ i, χ i (e x i)) * ψ (h * x)) =
      (∏ i, χ i (e h i))⁻¹ *
        ∑ x : T, (∏ i, χ i (e x i)) * ψ x := by
  classical
  have hbase := gauss_transform_finite_crt R e χ ψ hχ (1 : T)
  simp only [one_mul, map_one, Pi.one_apply, one_ne_zero, ↓reduceIte,
    inv_one, one_mul] at hbase
  rw [gauss_transform_finite_crt R e χ ψ hχ h, hbase]
  have hlocal (i : ι) :
      (if e h i = 0 then 0 else
        (χ i (e h i))⁻¹ * gaussSum (χ i) (coordinateAddChar R e ψ i)) =
      (χ i (e h i))⁻¹ * gaussSum (χ i) (coordinateAddChar R e ψ i) := by
    split_ifs with hi
    · simp [hi]
    · rfl
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]

theorem finite_prod_eq_iInf {ι A : Type*} [Fintype ι] [CommRing A]
    (P : ι → Ideal A) (hc : Pairwise (Function.onFun IsCoprime P)) :
    (∏ i, P i) = ⨅ i, P i := by
  simpa using (Ideal.prod_eq_iInf_of_pairwise_isCoprime
    (s := Finset.univ) (J := P) (by
      intro i _ j _ hij
      exact hc hij))

noncomputable def quotientProdEquivPi {ι A : Type*} [Fintype ι] [CommRing A]
    (P : ι → Ideal A) (hc : Pairwise (Function.onFun IsCoprime P)) :
    (A ⧸ ∏ i, P i) ≃+* ∀ i, A ⧸ P i :=
  (Ideal.quotEquivOfEq (finite_prod_eq_iInf P hc)).trans
    (Ideal.quotientInfRingEquivPiQuotient P hc)

@[simp] theorem quotientProdEquivPi_mk {ι A : Type*} [Fintype ι] [CommRing A]
    (P : ι → Ideal A) (hc : Pairwise (Function.onFun IsCoprime P))
    (a : A) (i : ι) :
    quotientProdEquivPi P hc (Ideal.Quotient.mk (∏ j, P j) a) i =
      Ideal.Quotient.mk (P i) a := by
  simp only [quotientProdEquivPi, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl

theorem gauss_transform_finite_ideal_crt {ι A : Type*} [Fintype ι] [CommRing A]
    (P : ι → Ideal A) (hc : Pairwise (Function.onFun IsCoprime P))
    [∀ i, (P i).IsMaximal]
    [Fintype (A ⧸ ∏ i, P i)] [∀ i, Fintype (A ⧸ P i)]
    (χ : ∀ i, MulChar (A ⧸ P i) ℂ)
    (ψ : AddChar (A ⧸ ∏ i, P i) ℂ) (hχ : ∀ i, χ i ≠ 1)
    (h : A ⧸ ∏ i, P i) :
    (∑ x : A ⧸ ∏ i, P i, (∏ i, χ i (quotientProdEquivPi P hc x i)) * ψ (h * x)) =
      ∏ i, if quotientProdEquivPi P hc h i = 0 then 0 else
        (χ i (quotientProdEquivPi P hc h i))⁻¹ *
          gaussSum (χ i) (coordinateAddChar (fun i => A ⧸ P i)
            (quotientProdEquivPi P hc) ψ i) := by
  let (i : ι) : Field (A ⧸ P i) := Ideal.Quotient.field (P i)
  exact gauss_transform_finite_crt (fun i => A ⧸ P i)
    (quotientProdEquivPi P hc) χ ψ hχ h

end IdealGaussCRT

end

end OAI

end


