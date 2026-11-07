-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CubeLabels
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_CubeLabels
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:04:22.363271+00:00
-- url     : https://prove2.me/theorems/cdf80f21-dfc4-47f3-b59c-09da55f9c27e
-- title:
--   Cube Labels
-- statement:
--   Definitions and structural lemmas for Cube Labels, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/CubeLabels.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_SquarefreeDivisors
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_mul
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicReflectionKernel.logSchwartz_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply


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
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
section
open scoped BigOperators Classical
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (crossSymbol quadraticCrossPhase)
def cubeOddSupport {ι : Type*} (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Finset ι :=
  B.filter fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val % 2 = 1
def mixedCubeCross {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (U B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) : ℂ :=
  ∏ i ∈ U, ∏ k ∈ B.filter (fun k => conductorExponent (parity (v k)) (ε₁ k) (ε₂ k) ≠ 0),
    crossSymbol p hg i k ^ (if side then 5 else 1) *
      crossSymbol p hg k i ^ (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val
end FirstPassCubeLabels
open scoped BigOperators Classical
open UniqueFactorizationMonoid
namespace QuadraticSquarefreeKernel
abbrev O := ActualEisensteinCubic.O
def squarePart (I : Ideal O) : Ideal O := (show ∃ a b : Ideal O, a ^ 2 * b = I ∧ Squarefree b from by
    induction I using WfDvdMonoid.induction_on_irreducible with
    | zero => exact ⟨0, 1, by simp, squarefree_one⟩
    | unit u hu => exact ⟨1, u, by simp only [one_pow, one_mul], hu.squarefree⟩
    | mul z p hz hp ih =>
      obtain ⟨a, b, hab, hb⟩ := ih
      by_cases hpb : p ∣ b
      · obtain ⟨c, hc⟩ := hpb
        refine ⟨p * a, c, ?_, hb.squarefree_of_dvd ⟨p, by rw [hc, mul_comm p c]⟩⟩
        rw [← hab, hc]
        simp only [mul_pow, pow_two]
        ac_rfl
      · refine ⟨a, p * b, ?_, squarefree_mul_iff.mpr
          ⟨hp.isRelPrime_iff_not_dvd.mpr hpb, hp.squarefree, hb⟩⟩
        rw [← hab]
        ac_rfl).choose
def squarefreePart (I : Ideal O) : Ideal O :=
  (show ∃ a b : Ideal O, a ^ 2 * b = I ∧ Squarefree b from by
    induction I using WfDvdMonoid.induction_on_irreducible with
    | zero => exact ⟨0, 1, by simp, squarefree_one⟩
    | unit u hu => exact ⟨1, u, by simp only [one_pow, one_mul], hu.squarefree⟩
    | mul z p hz hp ih =>
      obtain ⟨a, b, hab, hb⟩ := ih
      by_cases hpb : p ∣ b
      · obtain ⟨c, hc⟩ := hpb
        refine ⟨p * a, c, ?_, hb.squarefree_of_dvd ⟨p, by rw [hc, mul_comm p c]⟩⟩
        rw [← hab, hc]
        simp only [mul_pow, pow_two]
        ac_rfl
      · refine ⟨a, p * b, ?_, squarefree_mul_iff.mpr
          ⟨hp.isRelPrime_iff_not_dvd.mpr hpb, hp.squarefree, hb⟩⟩
        rw [← hab]
        ac_rfl).choose_spec.choose
theorem squarePart_sq_mul_squarefreePart (I : Ideal O) :
    squarePart I ^ 2 * squarefreePart I = I :=
  (show ∃ a b : Ideal O, a ^ 2 * b = I ∧ Squarefree b from by
    induction I using WfDvdMonoid.induction_on_irreducible with
    | zero => exact ⟨0, 1, by simp, squarefree_one⟩
    | unit u hu => exact ⟨1, u, by simp only [one_pow, one_mul], hu.squarefree⟩
    | mul z p hz hp ih =>
      obtain ⟨a, b, hab, hb⟩ := ih
      by_cases hpb : p ∣ b
      · obtain ⟨c, hc⟩ := hpb
        refine ⟨p * a, c, ?_, hb.squarefree_of_dvd ⟨p, by rw [hc, mul_comm p c]⟩⟩
        rw [← hab, hc]
        simp only [mul_pow, pow_two]
        ac_rfl
      · refine ⟨a, p * b, ?_, squarefree_mul_iff.mpr
          ⟨hp.isRelPrime_iff_not_dvd.mpr hpb, hp.squarefree, hb⟩⟩
        rw [← hab]
        ac_rfl).choose_spec.choose_spec.1
theorem squarefree_squarefreePart (I : Ideal O) : Squarefree (squarefreePart I) :=
  (show ∃ a b : Ideal O, a ^ 2 * b = I ∧ Squarefree b from by
    induction I using WfDvdMonoid.induction_on_irreducible with
    | zero => exact ⟨0, 1, by simp, squarefree_one⟩
    | unit u hu => exact ⟨1, u, by simp only [one_pow, one_mul], hu.squarefree⟩
    | mul z p hz hp ih =>
      obtain ⟨a, b, hab, hb⟩ := ih
      by_cases hpb : p ∣ b
      · obtain ⟨c, hc⟩ := hpb
        refine ⟨p * a, c, ?_, hb.squarefree_of_dvd ⟨p, by rw [hc, mul_comm p c]⟩⟩
        rw [← hab, hc]
        simp only [mul_pow, pow_two]
        ac_rfl
      · refine ⟨a, p * b, ?_, squarefree_mul_iff.mpr
          ⟨hp.isRelPrime_iff_not_dvd.mpr hpb, hp.squarefree, hb⟩⟩
        rw [← hab]
        ac_rfl).choose_spec.choose_spec.2
theorem squarePart_ne_zero {I : Ideal O} (hI : I ≠ 0) : squarePart I ≠ 0 := by
  intro hz
  have h := squarePart_sq_mul_squarefreePart I
  rw [hz, zero_pow (by decide : 2 ≠ 0), zero_mul] at h
  exact hI h.symm
theorem squarefree_decomposition_unique {A B D E : Ideal O}
    (hA : A ≠ 0) (hB : B ≠ 0) (hD : Squarefree D) (hE : Squarefree E)
    (h : A ^ 2 * D = B ^ 2 * E) : A = B ∧ D = E := by
  have hf := congrArg normalizedFactors h
  rw [normalizedFactors_mul (pow_ne_zero _ hA) hD.ne_zero,
    normalizedFactors_mul (pow_ne_zero _ hB) hE.ne_zero,
    normalizedFactors_pow, normalizedFactors_pow] at hf
  have hd := (squarefree_iff_nodup_normalizedFactors hD.ne_zero).mp hD
  have he := (squarefree_iff_nodup_normalizedFactors hE.ne_zero).mp hE
  have hcount (P : Ideal O) :
      (normalizedFactors A).count P = (normalizedFactors B).count P ∧
      (normalizedFactors D).count P = (normalizedFactors E).count P := by
    have hc := congrArg (Multiset.count P) hf
    simp only [Multiset.count_add, Multiset.count_nsmul] at hc
    have hd1 := Multiset.nodup_iff_count_le_one.mp hd P
    have he1 := Multiset.nodup_iff_count_le_one.mp he P
    omega
  constructor
  · apply associated_iff_eq.mp
    apply (associated_iff_normalizedFactors_eq_normalizedFactors hA hB).mpr
    exact Multiset.ext.mpr (fun P => (hcount P).1)
  · apply associated_iff_eq.mp
    apply (associated_iff_normalizedFactors_eq_normalizedFactors hD.ne_zero hE.ne_zero).mpr
    exact Multiset.ext.mpr (fun P => (hcount P).2)
theorem squarePart_mul_squarefree {A D : Ideal O} (hA : A ≠ 0) (hD : Squarefree D) :
    squarePart (A ^ 2 * D) = A ∧ squarefreePart (A ^ 2 * D) = D :=
  squarefree_decomposition_unique
    (squarePart_ne_zero (mul_ne_zero (pow_ne_zero _ hA) hD.ne_zero)) hA
    (squarefree_squarefreePart _) hD (squarePart_sq_mul_squarefreePart _)
def decompositionEquiv : {I : Ideal O // I ≠ 0} ≃
    {A : Ideal O // A ≠ 0} × {D : Ideal O // Squarefree D} where
  toFun I := (⟨squarePart I.val, squarePart_ne_zero I.property⟩,
    ⟨squarefreePart I.val, squarefree_squarefreePart I.val⟩)
  invFun p := ⟨p.1.val ^ 2 * p.2.val, mul_ne_zero (pow_ne_zero _ p.1.property) p.2.property.ne_zero⟩
  left_inv I := Subtype.ext (squarePart_sq_mul_squarefreePart I.val)
  right_inv p := by
    apply Prod.ext
    · exact Subtype.ext (squarePart_mul_squarefree p.1.property p.2.property).1
    · exact Subtype.ext (squarePart_mul_squarefree p.1.property p.2.property).2
open ActualEisensteinCubic QuadraticInitialBound CompletedGauss
theorem quadraticRow_mul {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (a b : O) :
    quadraticRow P hg S (a * b) = quadraticRow P hg S a * quadraticRow P hg S b := by
  rw [quadraticRow, finiteSquarefreeRow_mul, mul_pow]
  rfl
end QuadraticSquarefreeKernel
end
namespace QuadraticMainBoundary
open scoped BigOperators Classical
open UniqueFactorizationMonoid
abbrev O := ActualEisensteinCubic.O
open QuadraticSquarefreeKernel
def cutoffDifference (K : ℝ) (H D : Ideal O) : ℝ :=
  (if (Ideal.absNorm (H * D) : ℝ) ≤ K then 1 else 0) -
    (if (Ideal.absNorm H : ℝ) ≤ K then 1 else 0)
end QuadraticMainBoundary
open scoped BigOperators Classical
namespace QuadraticDivisorCancellation
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT QuadraticInitialBound QuadraticSquarefreeKernel
def normalizedRow {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (z : O) : ℂ :=
  quadraticRow P hg S z / (‖eisEmbedding z‖ : ℂ)
theorem normalizedRow_mul {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (a b : O) :
    normalizedRow P hg S (a * b) = normalizedRow P hg S a * normalizedRow P hg S b := by
  simp only [normalizedRow, quadraticRow_mul, map_mul, norm_mul, Complex.ofReal_mul,
    div_mul_div_comm]
theorem normalizedRow_one {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) : normalizedRow P hg S 1 = 1 := by
  simp [normalizedRow, quadraticRow, finiteSquarefreeRow]
def normalizedRowHom {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) : O →* ℂ where
  toFun := normalizedRow P hg S
  map_one' := normalizedRow_one P hg S
  map_mul' := normalizedRow_mul P hg S
end QuadraticDivisorCancellation
end
end OAI


