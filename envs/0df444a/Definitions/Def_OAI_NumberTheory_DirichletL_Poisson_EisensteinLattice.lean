-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_EisensteinLattice
-- name    : OAI_NumberTheory_DirichletL_Poisson_EisensteinLattice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:55:40.213824+00:00
-- url     : https://prove2.me/theorems/c6fcfba1-b003-49b4-a403-eedf3baf9a9f
-- title:
--   Eisenstein Lattice
-- statement:
--   Definitions and structural lemmas for Eisenstein Lattice, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/EisensteinLattice.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SecondPoissonScale
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


set_option autoImplicit false
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
def inverseJacobian (A : ℂ ≃L[ℝ] ℂ) : ℝ :=
  |(LinearMap.det (A : ℂ →ₗ[ℝ] ℂ))⁻¹|
def dualMap (A : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ :=
  A.symm.toContinuousLinearMap.adjoint
def translateSchwartz (f : 𝓢(ℂ, ℂ)) (b : ℂ) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun z : ℂ => z + b)
    (by fun_prop) (isometry_add_right b).antilipschitz f
@[simp] theorem translateSchwartz_apply (f : 𝓢(ℂ, ℂ)) (b z : ℂ) :
    translateSchwartz f b z = f (z + b) := rfl
def affinePullback (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A (translateSchwartz f b)
@[simp] theorem affinePullback_apply (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b z : ℂ) :
    affinePullback f A b z = f (A z + b) := rfl
end
section
open scoped RealInnerProductSpace
def basisMap (w : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp Complex.reCLM +
    w • (Complex.ofRealCLM.comp Complex.imCLM)
@[simp] theorem basisMap_apply (w z : ℂ) :
    basisMap w z = (z.re : ℂ) + w * (z.im : ℂ) := rfl
def basisEquiv (w : ℂ) (hw : w.im ≠ 0) : ℂ ≃L[ℝ] ℂ where
  toLinearEquiv :=
    { toLinearMap := (basisMap w).toLinearMap
      invFun z := complexPoint (z.re - z.im * w.re / w.im) (z.im / w.im)
      left_inv z := by
        change complexPoint ((basisMap w z).re - (basisMap w z).im * w.re / w.im)
          ((basisMap w z).im / w.im) = z
        apply Complex.ext
        · simp only [basisMap_apply, Complex.add_re, Complex.ofReal_re,
            Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero,
            Complex.add_im, Complex.mul_im,  zero_add, complexPoint]
          field_simp [hw]
          ring
        · simp [basisMap_apply, complexPoint, hw]
      right_inv z := by
        change basisMap w (complexPoint (z.re - z.im * w.re / w.im)
          (z.im / w.im)) = z
        apply Complex.ext
        · simp only [basisMap_apply, complexPoint, Complex.add_re, Complex.ofReal_re,
            Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero]
          field_simp [hw]
          ring
        · simp only [basisMap_apply, complexPoint, Complex.add_im,
            Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, mul_zero, zero_add]
          field_simp [hw] }
  continuous_toFun := (basisMap w).continuous
  continuous_invFun := by
    simp only [complexPoint_eq]
    fun_prop
@[simp] theorem basisEquiv_apply (w : ℂ) (hw : w.im ≠ 0) (z : ℂ) :
    basisEquiv w hw z = (z.re : ℂ) + w * (z.im : ℂ) := rfl
@[simp] theorem basisEquiv_symm_apply (w : ℂ) (hw : w.im ≠ 0) (z : ℂ) :
    (basisEquiv w hw).symm z =
      complexPoint (z.re - z.im * w.re / w.im) (z.im / w.im) := rfl
def complexMulEquiv (c : ℂ) (hc : c ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℂ) (Units.mk0 c hc)
@[simp] theorem complexMulEquiv_apply (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    complexMulEquiv c hc z = c * z := rfl
@[simp] theorem complexMulEquiv_symm_apply (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    (complexMulEquiv c hc).symm z = c⁻¹ * z := rfl
def scaledBasisEquiv (w : ℂ) (hw : w.im ≠ 0) (c : ℂ) (hc : c ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  (basisEquiv w hw).trans (complexMulEquiv c hc)
@[simp] theorem scaledBasisEquiv_apply (w : ℂ) (hw : w.im ≠ 0)
    (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    scaledBasisEquiv w hw c hc z = c * ((z.re : ℂ) + w * (z.im : ℂ)) := rfl
end
section
open MeasureTheory EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace
abbrev O := ActualEisensteinCubic.O
def eisensteinLatticeMap (c : ℂ) (hc : c ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  scaledBasisEquiv omega3 omega3_im_ne_zero c hc
def eisensteinDualFrequency (c : ℂ) (hc : c ≠ 0) (p : ℤ × ℤ) : ℂ :=
  dualMap (eisensteinLatticeMap c hc) (complexPoint (p.1 : ℝ) (p.2 : ℝ))
end
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace
def explicitDualFrequency (c : ℂ) (p : ℤ × ℤ) : ℂ :=
  complexPoint (p.1 : ℝ) (((p.1 : ℝ) + 2 * (p.2 : ℝ)) / Real.sqrt 3) /
    starRingEnd ℂ c
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
end IdealGaussCRT
end
end OAI


