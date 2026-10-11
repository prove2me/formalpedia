-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0059
-- name    : PNT_ZeroFree_433_0059
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T16:13:38.646856+00:00
-- url     : https://prove2.me/theorems/cb075a58-5ec1-4799-81e1-c40f4543a5c6
-- title:
--   Zero-free region foundations: Mellin.UniformKernelBounds [0059]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Mellin.UniformKernelBounds
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Mellin/UniformKernelBounds.lean#L364-L650

import Definitions.Def_PNT_ZeroFree_433_0059_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Mellin/UniformKernelBounds.lean
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

namespace CubicReflectionKernel
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set


theorem paperKernel_euler_source_uniform_weighted_bound
    (a b : ℝ) (ha : 0 < a) (A K : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ i ≤ K, ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperKernel W) i x‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  choose s c hc hb using fun i : Fin (K + 1) => paperKernel_euler_source_power_decay a b ha A i.val
  let S : Finset (ℕ × ℕ) := Finset.univ.biUnion s
  let D : ℝ := (∑ i : Fin (K + 1), c i) + 1
  have hD : 0 < D := by
    have hs : (0 : ℝ) ≤ ∑ i : Fin (K + 1), c i := Finset.sum_nonneg (fun i _ => (hc i).le)
    dsimp [D]
    linarith
  have hci (i : Fin (K + 1)) : c i ≤ D := by
    have hs : c i ≤ ∑ k : Fin (K + 1), c k :=
      Finset.single_le_sum (fun k _ => (hc k).le) (Finset.mem_univ i)
    dsimp [D]
    linarith
  refine ⟨S, 2 ^ A * (D + D), by positivity, ?_⟩
  intro W hsupp
  let Q := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hsource (i : Fin (K + 1)) : c i * (s i).sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ D * Q := by
    have hsub : s i ⊆ S := Finset.subset_biUnion_of_mem s (Finset.mem_univ i)
    have hq : (s i).sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
      Seminorm.le_def.mp (Finset.sup_mono hsub) W
    exact mul_le_mul (hci i) hq (by positivity) hD.le
  have hsmall : ∀ i ≤ K, ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖LocalLogFourier.eulerDeriv (paperKernel W) i x‖ ≤ D * Q := by
    intro i hi x hx hx1
    let k : Fin (K + 1) := ⟨i, by omega⟩
    have hp : x ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hx.le hx1 (by norm_num)
    calc
      _ ≤ (c k * (s k).sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * x ^ (1 / 4 : ℝ) := (hb k W hsupp x hx).1
      _ ≤ c k * (s k).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
        simpa using mul_le_mul_of_nonneg_left hp (mul_nonneg (hc k).le (by positivity))
      _ ≤ D * Q := hsource k
  have hlarge : ∀ i ≤ K, ∀ x : ℝ, 1 ≤ x →
      x ^ A * ‖LocalLogFourier.eulerDeriv (paperKernel W) i x‖ ≤ D * Q := by
    intro i hi x hx1
    have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    let k : Fin (K + 1) := ⟨i, by omega⟩
    have hxpow : x ^ A ≠ 0 := pow_ne_zero A hx.ne'
    calc
      _ ≤ x ^ A * ((c k * (s k).sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * x ^ (-(A : ℝ))) :=
        mul_le_mul_of_nonneg_left (hb k W hsupp x hx).2 (pow_nonneg hx.le A)
      _ = c k * (s k).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
        rw [Real.rpow_neg hx.le, Real.rpow_natCast]
        field_simp
      _ ≤ D * Q := hsource k
  intro i hi x hx
  have hh := LocalLogFourier.euler_two_regime_bound (paperKernel W) A K (D * Q) (D * Q)
    (mul_nonneg hD.le hQ) (mul_nonneg hD.le hQ) hsmall hlarge i hi x hx
  convert! hh using 1 ; dsimp [Q] ; ring

end CubicReflectionKernel

open scoped BigOperators Classical
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (crossSymbol quadraticCrossPhase columnPrimeCoprime)
open FiniteGaussPhase (canonicalProductGauss canonicalProductGauss_cross_factors)
open MixedGaussConversion (localGauss)

def gaussBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ) : ℂ :=
  ∏ i ∈ S, (∏ k ∈ S.erase i, crossSymbol p hg i k ^ e i) *
    localGauss (p i) (hp i) (hg i) (e i)

theorem canonicalProductGauss_eq_gaussBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ)
    (he : ∀ i ∈ S, e i ≠ 0) :
    canonicalProductGauss (fun i : S => p i.val) (fun i => hp i.val)
      (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => e i.val) =
      gaussBlock p hp hg S e := by
  let : DecidableEq S := fun a b => Classical.propDecidable (a = b)
  rw [canonicalProductGauss_cross_factors, ← Finset.prod_mul_distrib]
  have hin (i : S) :
      (∏ k ∈ (Finset.univ : Finset S).erase i,
        (canonicalSextic (Ideal.span {p i.val}) (hg i.val) ^ e i.val)
          (Ideal.Quotient.mk (Ideal.span {p i.val}) (p k.val))) =
      ∏ k ∈ S.erase i.val, crossSymbol p hg i.val k ^ e i.val := by
    apply Finset.prod_bij (fun k _ => k.val)
    · intro k hk
      exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hk).1 (Subtype.ext h), k.property⟩
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro k hk
      refine ⟨⟨k, (Finset.mem_erase.mp hk).2⟩, ?_, rfl⟩
      exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hk).1 (congrArg Subtype.val h),
        Finset.mem_univ _⟩
    · intro k hk
      exact MulChar.pow_apply' _ (he i.val i.property) _
  calc
    _ = ∏ i : S, (∏ k ∈ S.erase i.val, crossSymbol p hg i.val k ^ e i.val) *
        localGauss (p i.val) (hp i.val) (hg i.val) (e i.val) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hin i]
      rfl
    _ = _ := Finset.prod_coe_sort S (fun i =>
      (∏ k ∈ S.erase i, crossSymbol p hg i k ^ e i) * localGauss (p i) (hp i) (hg i) (e i))

def blockCross {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) (e : ι → ℕ) : ℂ :=
  ∏ i ∈ S, ∏ k ∈ T,
    crossSymbol p hg i k ^ e i * crossSymbol p hg k i ^ e k

theorem gaussBlock_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) (hd : Disjoint S T)
    (e : ι → ℕ) :
    gaussBlock p hp hg (S ∪ T) e =
      gaussBlock p hp hg S e * gaussBlock p hp hg T e * blockCross p hg S T e := by
  have hS (i : ι) (hi : i ∈ S) :
      (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) =
      (∏ k ∈ S.erase i, crossSymbol p hg i k ^ e i) *
        ∏ k ∈ T, crossSymbol p hg i k ^ e i := by
    have hn : i ∉ T := fun h => Finset.disjoint_left.mp hd hi h
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hn,
      Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hT (i : ι) (hi : i ∈ T) :
      (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) =
      (∏ k ∈ T.erase i, crossSymbol p hg i k ^ e i) *
        ∏ k ∈ S, crossSymbol p hg i k ^ e i := by
    have hn : i ∉ S := fun h => Finset.disjoint_left.mp hd h hi
    rw [Finset.union_comm S T, Finset.erase_union_distrib, Finset.erase_eq_of_notMem hn,
      Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
  have hpS : (∏ i ∈ S, (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) *
      localGauss (p i) (hp i) (hg i) (e i)) =
      gaussBlock p hp hg S e * (∏ i ∈ S, ∏ k ∈ T, crossSymbol p hg i k ^ e i) := by
    rw [gaussBlock, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hS i hi]
    ring
  have hpT : (∏ i ∈ T, (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) *
      localGauss (p i) (hp i) (hg i) (e i)) =
      gaussBlock p hp hg T e * (∏ i ∈ T, ∏ k ∈ S, crossSymbol p hg i k ^ e i) := by
    rw [gaussBlock, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hT i hi]
    ring
  rw [gaussBlock, Finset.prod_union hd, hpS, hpT,
    Finset.prod_comm (s := T) (t := S)]
  simp only [blockCross, Finset.prod_mul_distrib]
  ring

theorem gaussBlock_congr {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e f : ι → ℕ)
    (he : ∀ i ∈ S, e i = f i) : gaussBlock p hp hg S e = gaussBlock p hp hg S f := by
  apply Finset.prod_congr rfl
  intro i hi
  rw [he i hi]

def cubeActiveSupport {ι : Type*} (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Finset ι :=
  B.filter (fun k => conductorExponent (parity (v k)) (ε₁ k) (ε₂ k) ≠ 0)

def blockCubeExponent {ι : Type*} [DecidableEq ι] (U : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) (i : ι) : ℕ :=
  if i ∈ U then (if side then 5 else 1)
  else (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val

theorem gaussBlock_cube_partition {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (U B : Finset ι) (hd : Disjoint U B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) :
    gaussBlock p hp hg (U ∪ cubeActiveSupport B v ε₁ ε₂)
      (blockCubeExponent U v ε₁ ε₂ side) =
    gaussBlock p hp hg U (fun _ => if side then 5 else 1) *
      gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
        (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
      mixedCubeCross p hg U B v ε₁ ε₂ side := by
  have hdc : Disjoint U (cubeActiveSupport B v ε₁ ε₂) := hd.mono_right (Finset.filter_subset _ _)
  have hU : ∀ i ∈ U, blockCubeExponent U v ε₁ ε₂ side i = (if side then 5 else 1) := by
    intro i hi
    simp only [blockCubeExponent, if_pos hi]
  have hB : ∀ i ∈ cubeActiveSupport B v ε₁ ε₂, blockCubeExponent U v ε₁ ε₂ side i =
      (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val := by
    intro i hi
    exact if_neg (fun hu => Finset.disjoint_left.mp hdc hu hi)
  rw [gaussBlock_union p hp hg U _ hdc,
    gaussBlock_congr p hp hg U _ _ hU, gaussBlock_congr p hp hg _ _ _ hB]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro k hk
  rw [hU i hi, hB k hk]

theorem canonicalProductGauss_cube_partition {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (U B : Finset ι) (hd : Disjoint U B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) :
    canonicalProductGauss (fun i : ↥(U ∪ cubeActiveSupport B v ε₁ ε₂) => p i.val)
      (fun i => hp i.val) (columnPrimeCoprime p hcop _) (fun i => hg i.val)
      (fun i => blockCubeExponent U v ε₁ ε₂ side i.val) =
    gaussBlock p hp hg U (fun _ => if side then 5 else 1) *
      gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
        (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
      ((if side then star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U
          (crtLabel p B v ε₁ ε₂ side))
        else finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U
          (crtLabel p B v ε₁ ε₂ side)) *
        quadraticCrossPhase p hg U (cubeOddSupport B v ε₁ ε₂)) := by
  have he : ∀ i ∈ U ∪ cubeActiveSupport B v ε₁ ε₂, blockCubeExponent U v ε₁ ε₂ side i ≠ 0 := by
    intro i hi
    by_cases hiU : i ∈ U
    · cases side <;> simp [blockCubeExponent, hiU]
    · have hiB := (Finset.mem_union.mp hi).resolve_left hiU
      simp only [blockCubeExponent, if_neg hiU]
      exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hiB).2
  rw [canonicalProductGauss_eq_gaussBlock p hp hcop hg _ _ he,
    gaussBlock_cube_partition p hp hg U B hd,
    mixedCubeCross_eq_row_quadratic p hcop hg hpr U B hd]

theorem columnCoefficient_eq_gaussBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) :
    MixedCrossSeparation.columnCoefficient p hp hcop hg S =
      star (FiniteGaussPhase.angularFactor (∏ i ∈ S, p i)) *
        gaussBlock p hp hg S (fun _ => 2) := by
  unfold MixedCrossSeparation.columnCoefficient FiniteGaussPhase.canonicalProductCoefficient
  rw [Finset.prod_coe_sort]
  rw [canonicalProductGauss_eq_gaussBlock p hp hcop hg S (fun _ => 2) (fun _ _ => by decide)]

theorem blockCross_two_eq_row_four {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) :
    blockCross p hg S T (fun _ => 2) =
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (∏ k ∈ T, p k) ^ 4 := by
  simp only [blockCross, finiteSquarefreeRow, map_prod, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro k hk
  have hr : crossSymbol p hg i k ^ 2 = crossSymbol p hg k i ^ 2 :=
    canonicalSextic_sq_reciprocity_primary (Ideal.span {p i}) (Ideal.span {p k})
      (hg i) (hg k) (p i) (p k) rfl rfl (hpr i) (hpr k)
  change crossSymbol p hg i k ^ 2 * crossSymbol p hg k i ^ 2 = crossSymbol p hg i k ^ 4
  rw [← hr]
  ring

theorem columnCoefficient_union_row_four {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) (hd : Disjoint S T) :
    MixedCrossSeparation.columnCoefficient p hp hcop hg (S ∪ T) =
      MixedCrossSeparation.columnCoefficient p hp hcop hg S *
        MixedCrossSeparation.columnCoefficient p hp hcop hg T *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (∏ k ∈ T, p k) ^ 4 := by
  have ha : FiniteGaussPhase.angularFactor (∏ i ∈ S ∪ T, p i) =
      FiniteGaussPhase.angularFactor (∏ i ∈ S, p i) *
        FiniteGaussPhase.angularFactor (∏ i ∈ T, p i) := by
    rw [Finset.prod_union hd]
    simp only [FiniteGaussPhase.angularFactor, map_mul, norm_mul, Complex.ofReal_mul,
      div_eq_mul_inv, mul_inv_rev]
    ring
  rw [columnCoefficient_eq_gaussBlock, columnCoefficient_eq_gaussBlock,
    columnCoefficient_eq_gaussBlock, ha, star_mul, gaussBlock_union p hp hg S T hd,
    blockCross_two_eq_row_four p hg hpr S T]
  ring

theorem gaussBlock_norm_one {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (S : Finset ι) (e : ι → ℕ) (he : ∀ i ∈ S, e i ≠ 0) (he6 : ∀ i ∈ S, e i < 6) :
    ‖gaussBlock p hp hg S e‖ = 1 := by
  rw [← canonicalProductGauss_eq_gaussBlock p hp hcop hg S e he]
  exact FiniteGaussPhase.norm_canonicalProductGauss
    (fun i : S => p i.val) (fun i => hp i.val) (columnPrimeCoprime p hcop S)
    (fun i => hg i.val) (fun i => hc i.val) (fun i => e i.val)
    (fun i => he i.val i.property) (fun i => he6 i.val i.property)

end FirstPassCubeLabels

end

end OAI

end


