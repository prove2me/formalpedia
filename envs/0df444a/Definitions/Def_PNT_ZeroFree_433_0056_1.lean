-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0056_1
-- name    : PNT_ZeroFree_433_0056_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T15:50:21.167834+00:00
-- url     : https://prove2.me/theorems/ef57560d-fc8a-4ca7-9410-a44ac4ec2351
-- title:
--   Zero-free region foundations: CubicSieve.CubeLabels [0056_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.CubeLabels
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/CubeLabels.lean#L79-L352

import Definitions.Def_PNT_ZeroFree_433_0054
import Definitions.Def_PNT_ZeroFree_433_0055

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/CubeLabels.lean
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

 theorem cross_sixth {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (i k : ι) (hik : i ≠ k) :
    crossSymbol p hg i k ^ 6 = 1 := by
  have hnot : p k ∉ Ideal.span {p i} := by
    intro hm
    have hle : Ideal.span {p k} ≤ Ideal.span {p i} :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    have ht := (hcop hik).sup_eq
    rw [sup_eq_left.mpr hle] at ht
    exact (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top ht
  simpa only [crossSymbol, map_pow, if_neg hnot] using
    canonicalSextic_sixth_power_mask (Ideal.span {p i}) (hg i) (p k)

theorem reverse_cross_eq_quadratic {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (i k : ι) (hik : i ≠ k) :
    crossSymbol p hg k i = crossSymbol p hg i k *
      (crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3) := by
  have hr : crossSymbol p hg i k ^ 2 = crossSymbol p hg k i ^ 2 :=
    canonicalSextic_sq_reciprocity_primary (Ideal.span {p i}) (Ideal.span {p k})
      (hg i) (hg k) (p i) (p k) rfl rfl (hpr i) (hpr k)
  symm
  calc
    _ = crossSymbol p hg i k ^ 4 *
        (crossSymbol p hg k i ^ 2 * crossSymbol p hg k i) := by ring
    _ = crossSymbol p hg i k ^ 6 * crossSymbol p hg k i := by rw [← hr]; ring
    _ = _ := by rw [cross_sixth p hcop hg i k hik, one_mul]

 theorem local_quadratic_sq {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (i k : ι) (hik : i ≠ k) :
    (crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3) ^ 2 = 1 := by
  rw [mul_pow, ← pow_mul, ← pow_mul]
  norm_num only [show 3 * 2 = 6 by decide, cross_sixth p hcop hg i k hik,
    cross_sixth p hcop hg k i hik.symm, one_mul]

 theorem crt_exponent_table (side parityBit ε₁ ε₂ : Bool)
    (he : conductorExponent parityBit ε₁ ε₂ ≠ 0) :
    ((if side then 5 else 1) + (conductorExponent parityBit ε₁ ε₂).val) % 6 =
      ((if side then 5 else 1) * crtExponent side parityBit ε₁ ε₂) % 6 := by
  cases side <;> cases parityBit <;> cases ε₁ <;> cases ε₂ <;>
    first | exact False.elim (he (by decide)) | decide

theorem active_cube_cross_local {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (i k : ι) (hik : i ≠ k)
    (side parityBit ε₁ ε₂ : Bool) (he : conductorExponent parityBit ε₁ ε₂ ≠ 0) :
    crossSymbol p hg i k ^ (if side then 5 else 1) *
      crossSymbol p hg k i ^ (conductorExponent parityBit ε₁ ε₂).val =
    (if side then star (crossSymbol p hg i k ^ crtExponent side parityBit ε₁ ε₂)
      else crossSymbol p hg i k ^ crtExponent side parityBit ε₁ ε₂) *
      (crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3) ^
        (conductorExponent parityBit ε₁ ε₂).val := by
  let x := crossSymbol p hg i k
  let q := crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3
  have hrev : crossSymbol p hg k i = x * q := reverse_cross_eq_quadratic p hcop hg hpr i k hik
  have h6 : x ^ 6 = 1 := cross_sixth p hcop hg i k hik
  have hs : star x = x ^ 5 := by
    have h := canonicalSextic_conj_as_row_label (Ideal.span {p i}) (hg i) (p k)
    change star x = x * x ^ 4 at h
    rw [h]
    ring
  calc
    _ = x ^ ((if side then 5 else 1) + (conductorExponent parityBit ε₁ ε₂).val) *
        q ^ (conductorExponent parityBit ε₁ ε₂).val := by rw [hrev, mul_pow, pow_add]; ring
    _ = _ := by
      congr 1
      cases side
      · change x ^ (1 + (conductorExponent parityBit ε₁ ε₂).val) = x ^ crtExponent false parityBit ε₁ ε₂
        conv_lhs => rw [pow_eq_pow_mod _ h6]
        conv_rhs => rw [pow_eq_pow_mod _ h6]
        congr 1
        simpa only [Bool.false_eq_true, ↓reduceIte, one_mul] using crt_exponent_table false parityBit ε₁ ε₂ he
      · change x ^ (5 + (conductorExponent parityBit ε₁ ε₂).val) = star (x ^ crtExponent true parityBit ε₁ ε₂)
        rw [star_pow, hs, ← pow_mul]
        conv_lhs => rw [pow_eq_pow_mod _ h6]
        conv_rhs => rw [pow_eq_pow_mod _ h6]
        congr 1
        exact crt_exponent_table true parityBit ε₁ ε₂ he

def cubeOddSupport {ι : Type*} (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Finset ι :=
  B.filter fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val % 2 = 1

def mixedCubeCross {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (U B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) : ℂ :=
  ∏ i ∈ U, ∏ k ∈ B.filter (fun k => conductorExponent (parity (v k)) (ε₁ k) (ε₂ k) ≠ 0),
    crossSymbol p hg i k ^ (if side then 5 else 1) *
      crossSymbol p hg k i ^ (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val

theorem mixedCubeCross_eq_ordered {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (U B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) :
    mixedCubeCross p hg U B v ε₁ ε₂ side =
      (∏ i ∈ U, ∏ k ∈ B.filter (fun k => conductorExponent (parity (v k)) (ε₁ k) (ε₂ k) ≠ 0),
        crossSymbol p hg i k ^ (if side then 5 else 1)) *
      (∏ k ∈ B.filter (fun k => conductorExponent (parity (v k)) (ε₁ k) (ε₂ k) ≠ 0),
        ∏ i ∈ U, crossSymbol p hg k i ^ (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) := by
  rw [Finset.prod_comm (s := B.filter _) (t := U)]
  simp only [mixedCubeCross, Finset.prod_mul_distrib]

 theorem cube_cross_local_if {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (i k : ι) (hik : i ≠ k)
    (side parityBit ε₁ ε₂ : Bool) :
    (if conductorExponent parityBit ε₁ ε₂ ≠ 0 then
      crossSymbol p hg i k ^ (if side then 5 else 1) *
        crossSymbol p hg k i ^ (conductorExponent parityBit ε₁ ε₂).val else 1) =
    (if side then star (crossSymbol p hg i k ^ crtExponent side parityBit ε₁ ε₂)
      else crossSymbol p hg i k ^ crtExponent side parityBit ε₁ ε₂) *
      (if (conductorExponent parityBit ε₁ ε₂).val % 2 = 1 then
        crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3 else 1) := by
  by_cases he : conductorExponent parityBit ε₁ ε₂ = 0
  · simp [he, crtExponent]
  · rw [if_pos he, active_cube_cross_local p hcop hg hpr i k hik side parityBit ε₁ ε₂ he]
    congr 1
    rw [pow_eq_pow_mod _ (local_quadratic_sq p hcop hg i k hik)]
    by_cases ho : (conductorExponent parityBit ε₁ ε₂).val % 2 = 1
    · simp [ho]
    · have hz : (conductorExponent parityBit ε₁ ε₂).val % 2 = 0 := by omega
      simp [ hz]

theorem mixedCubeCross_eq_row_quadratic {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (U B : Finset ι) (hd : Disjoint U B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) :
    mixedCubeCross p hg U B v ε₁ ε₂ side =
      (if side then star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U
          (crtLabel p B v ε₁ ε₂ side))
        else finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U
          (crtLabel p B v ε₁ ε₂ side)) *
      quadraticCrossPhase p hg U (cubeOddSupport B v ε₁ ε₂) := by
  have hr : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U
      (crtLabel p B v ε₁ ε₂ side) =
      ∏ i ∈ U, ∏ k ∈ B, crossSymbol p hg i k ^
        crtExponent side (parity (v k)) (ε₁ k) (ε₂ k) := by
    simp only [finiteSquarefreeRow, crtLabel, primeProduct, map_prod, map_pow, crossSymbol]
  calc
    _ = (∏ i ∈ U, ∏ k ∈ B,
        if side then star (crossSymbol p hg i k ^ crtExponent side (parity (v k)) (ε₁ k) (ε₂ k))
        else crossSymbol p hg i k ^ crtExponent side (parity (v k)) (ε₁ k) (ε₂ k)) *
      (∏ i ∈ U, ∏ k ∈ B,
        if (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val % 2 = 1 then
          crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3 else 1) := by
      simp only [mixedCubeCross, Finset.prod_filter, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      apply Finset.prod_congr rfl
      intro k hk
      apply cube_cross_local_if p hcop hg hpr i k
      exact fun he => Finset.disjoint_left.mp hd hi (he ▸ hk)
    _ = _ := by
      congr 1
      · rw [hr]
        cases side <;> simp only [Bool.false_eq_true, ↓reduceIte, star_prod]
      · simp only [quadraticCrossPhase, cubeOddSupport, Finset.prod_filter]

theorem mixedCubeCross_eq_ray_expansion {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (U B : Finset ι) (hd : Disjoint U B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) :
    mixedCubeCross p hg U B v ε₁ ε₂ side =
      (if side then star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U
          (crtLabel p B v ε₁ ε₂ side))
        else finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U
          (crtLabel p B v ε₁ ε₂ side)) *
      (∑ χ : RayFourExpansion.RayCharacter, ∑ η : RayFourExpansion.RayCharacter,
        RayFourExpansion.crossCoeff χ η * RayFourExpansion.rayCharacter χ (∏ i ∈ U, p i) *
          RayFourExpansion.rayCharacter η (∏ k ∈ cubeOddSupport B v ε₁ ε₂, p k)) := by
  rw [mixedCubeCross_eq_row_quadratic p hcop hg hpr U B hd v ε₁ ε₂ side,
    RayFourExpansion.quadraticCrossPhase_character_expansion p hp hcop hg hc]
  exact hd.mono_right (Finset.filter_subset _ _)

end FirstPassCubeLabels

open scoped BigOperators Classical
open UniqueFactorizationMonoid
namespace QuadraticSquarefreeKernel
abbrev O := ActualEisensteinCubic.O

def squarePart (I : Ideal O) : Ideal O := (exists_sq_mul_squarefree I).choose

def squarefreePart (I : Ideal O) : Ideal O :=
  (exists_sq_mul_squarefree I).choose_spec.choose

theorem squarePart_sq_mul_squarefreePart (I : Ideal O) :
    squarePart I ^ 2 * squarefreePart I = I :=
  (exists_sq_mul_squarefree I).choose_spec.choose_spec.1

theorem squarefree_squarefreePart (I : Ideal O) : Squarefree (squarefreePart I) :=
  (exists_sq_mul_squarefree I).choose_spec.choose_spec.2

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

theorem squarefree_decomposition_tsum {V : Type*} [AddCommMonoid V] [TopologicalSpace V]
    (f : Ideal O → V) :
    (∑' I : {I : Ideal O // I ≠ 0}, f I.val) =
      ∑' p : {A : Ideal O // A ≠ 0} × {D : Ideal O // Squarefree D},
        f (p.1.val ^ 2 * p.2.val) := by
  exact (decompositionEquiv.symm.tsum_eq (fun I => f I.val)).symm

theorem norm_decomposition (I : Ideal O) :
    Ideal.absNorm (squarePart I) ^ 2 * Ideal.absNorm (squarefreePart I) = Ideal.absNorm I := by
  simpa only [map_mul, map_pow] using congrArg Ideal.absNorm (squarePart_sq_mul_squarefreePart I)

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

open QuadraticSquarefreeKernel


end QuadraticMainBoundary

open scoped BigOperators Classical
namespace QuadraticDivisorCancellation

open ActualEisensteinCubic ConcreteTraceCRT QuadraticInitialBound QuadraticSquarefreeKernel


end QuadraticDivisorCancellation

end

end OAI

end


