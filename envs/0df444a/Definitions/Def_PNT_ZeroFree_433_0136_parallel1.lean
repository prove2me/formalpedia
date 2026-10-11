-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0136_parallel1
-- name    : PNT_ZeroFree_433_0136_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:54:52.41935+00:00
-- url     : https://prove2.me/theorems/0f8c2cf6-5b4b-4676-ae14-88a83d9a38b0
-- title:
--   Zero-free region foundations: QuadraticSieve.AnnularLifting [0136_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.AnnularLifting
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/AnnularLifting.lean#L82-L653

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0065_1
import Definitions.Def_PNT_ZeroFree_433_0082
import Definitions.Def_PNT_ZeroFree_433_0086
import Definitions.Def_PNT_ZeroFree_433_0130_parallel1
import Definitions.Def_PNT_ZeroFree_433_0158_parallel1
import Definitions.Def_PNT_ZeroFree_433_0188_parallel1
import Definitions.Def_PNT_ZeroFree_433_0218_parallel1
import Definitions.Def_PNT_ZeroFree_433_0228_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0260_parallel1
import Definitions.Def_PNT_ZeroFree_433_0262_parallel1
import Definitions.Def_PNT_ZeroFree_433_0303_parallel1
import Definitions.Def_PNT_ZeroFree_433_0329_parallel1
import Definitions.Def_PNT_ZeroFree_433_0330_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/AnnularLifting.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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
open scoped BigOperators

section

open scoped BigOperators Classical

section
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss QuadraticSquarefreeKernel

def squarefreeHighRange (M K : ℝ) : Finset (Ideal O) :=
  (idealRange M).filter (fun I => K<(Ideal.absNorm I:ℝ))


lemma exists_lifted_annular_scale (M x : ℝ) (hM : 0<M) (hx : M<x) (hupper : x≤49*M) :
    ∃j : Fin 7, ((2:ℝ)^j.val*M)/2≤x ∧ x≤(2:ℝ)^j.val*M := by
  have hratio : 1≤x/M := (le_div_iff₀ hM).mpr (by linarith)
  obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near hratio (by norm_num : (1:ℝ)<2)
  have hratioU : x/M≤49 := (div_le_iff₀ hM).mpr hupper
  have hk : k<6 := by
    by_contra hn
    have h6 : 6≤k := by omega
    have hp : (2:ℝ)^6≤(2:ℝ)^k := pow_le_pow_right₀ (by norm_num) h6
    norm_num at hp
    linarith
  refine ⟨⟨k+1,by omega⟩,?_,?_⟩
  · have hl := (le_div_iff₀ hM).mp hlo
    simpa only [pow_succ,mul_assoc,mul_div_assoc,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)] using hl
  · exact ((div_lt_iff₀ hM).mp hhi).le

lemma sum_injective_mask_le {ι : Type*} [Fintype ι]
    (f : ι → Ideal O) (hf : Function.Injective f) (S : Finset (Ideal O))
    (v : Ideal O → ℝ) (hv : ∀I, 0≤v I) :
    (∑i, if f i∈S then v (f i) else 0)≤∑I∈S,v I := by
  classical
  rw [←Finset.sum_filter]
  rw [←Finset.sum_image (f := v) (g := f) (by intro i hi j hj he; exact hf he)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro I hI
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    exact (Finset.mem_filter.mp hi).2
  · intro I hI hnot
    exact hv I


end


section
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss FiniteSieveOperator

def ballQuadraticEnergy (M N : ℝ) (a : idealRange N → ℂ) : ℝ :=
  ∑I : idealRange M, ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J‖^2

theorem ballQuadraticEnergy_low_high (M N K : ℝ) (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ sieveNorm K N*(∑J, ‖a J‖^2) +
      ∑I : squarefreeHighRange M K, ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J‖^2 := by
  classical
  let E := fun I : Ideal O => ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I)*a J‖^2
  have hs : (idealRange M).filter (fun I => (Ideal.absNorm I:ℝ)≤K) ⊆ idealRange K := by
    intro I hI
    exact mem_idealRange.mpr ⟨(mem_idealRange.mp (Finset.mem_filter.mp hI).1).1,(Finset.mem_filter.mp hI).2⟩
  have hlo : (∑I∈(idealRange M).filter (fun I => (Ideal.absNorm I:ℝ)≤K), E I) ≤
      sieveNorm K N*(∑J, ‖a J‖^2) := by
    calc
      _ ≤ ∑I∈idealRange K,E I := Finset.sum_le_sum_of_subset_of_nonneg hs (fun I hI hnot => sq_nonneg _)
      _ = ballQuadraticEnergy K N a := (Finset.sum_coe_sort (idealRange K) E).symm
      _ ≤ _ := FiniteSieveOperator.energy_bound (matrix K N) a
  change (∑I : idealRange M,E I.val)≤_+(∑I : squarefreeHighRange M K,E I.val)
  rw [Finset.sum_coe_sort (idealRange M) E,
    ←Finset.sum_filter_add_sum_filter_not (idealRange M) (fun I => (Ideal.absNorm I:ℝ)≤K) E]
  rw [Finset.sum_coe_sort (squarefreeHighRange M K) E]
  simp only [not_le,squarefreeHighRange]
  linarith


end

open ActualEisensteinCubic CompletedGauss

theorem ballQuadraticEnergy_mono {M M' N : ℝ} (hM : M≤M') (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a≤ballQuadraticEnergy M' N a := by
  unfold ballQuadraticEnergy
  rw [Finset.sum_coe_sort (idealRange M)
    (fun I => ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I)*a J‖^2),
    Finset.sum_coe_sort (idealRange M')
    (fun I => ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I)*a J‖^2)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (idealRange_mono hM) (fun I hI hnot => sq_nonneg _)


end

section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss
open IdealCoprimeSieveOperator DivisorBlockCauchy

theorem gcdPool_admissible {n : Type*} [Fintype n] (cols : n → Ideal O)
    (hcols : ∀j, Admissible (cols j)) (D : Ideal O) (hD : D∈gcdPool cols) : Admissible D := by
  obtain ⟨⟨j,k⟩,_,rfl⟩ := Finset.mem_image.mp hD
  exact admissible_of_dvd (hcols j) (GCDMonoid.gcd_dvd_left _ _)


end

section

def cutoffRescaleCoefficient (C η r q : ℝ) : ℝ := C*r*q^2/(r/q)^η

theorem cutoffRescaleCoefficient_eq (C η r q : ℝ) (hr : 0<r) (hq : 0<q) :
    cutoffRescaleCoefficient C η r q=C*r^(1-η)*q^(2+η) := by
  rw [cutoffRescaleCoefficient,Real.div_rpow hr.le hq.le,
    Real.rpow_sub hr,Real.rpow_one,Real.rpow_add hq,Real.rpow_two]
  have hrp : r^η≠0 := (Real.rpow_pos_of_pos hr η).ne'
  have hqp : q^η≠0 := (Real.rpow_pos_of_pos hq η).ne'
  field_simp

theorem cutoffRescaleCoefficient_bounds (C η r q : ℝ)
    (hC : 0≤C) (hη : 0≤η) (hη1 : η≤1) (hr : 1≤r) (hr64 : r≤64) (hq : 1≤q) (hq7 : q≤7) :
    C≤cutoffRescaleCoefficient C η r q ∧ cutoffRescaleCoefficient C η r q≤21952*C := by
  rw [cutoffRescaleCoefficient_eq C η r q (by linarith) (by linarith)]
  have hrlo : 1≤r^(1-η) := Real.one_le_rpow hr (by linarith)
  have hqlo : 1≤q^(2+η) := Real.one_le_rpow hq (by linarith)
  have hrup : r^(1-η)≤r := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hr (show 1-η≤1 by linarith)
  have hqup : q^(2+η)≤q^3 := by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le hq (show 2+η≤(3:ℝ) by linarith)
  constructor
  · calc
      C = C*1*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      _ ≤ C*r*q^3 := by gcongr
      _ ≤ C*64*7^3 := by gcongr
      _ = _ := by ring

theorem selectedPoissonK_rescale (C M X η r q : ℝ)
    (hM : 0<M) (hX : 0<X) (hr : 0<r) (hq : 0<q) :
    selectedPoissonK (cutoffRescaleCoefficient C η r q) (r*M) (X/q) η =
      selectedPoissonK C M X η := by
  unfold selectedPoissonK selectedPoissonT cutoffRescaleCoefficient
  have he : (r*M)*(X/q)=(r/q)*(M*X) := by ring
  rw [he,Real.mul_rpow (by positivity : 0≤r/q) (by positivity : 0≤M*X)]
  have hp : (r/q)^η≠0 := (Real.rpow_pos_of_pos (by positivity) η).ne'
  field_simp

end

open scoped BigOperators Classical

def largeGcdThreshold (α N : ℝ) : ℝ := N^(1-1/α)

theorem largeGcdThreshold_quotient_power (α N : ℝ) (hα : α≠0) (hN : 0<N) :
    (N/largeGcdThreshold α N)^α=N := by
  have he : N/largeGcdThreshold α N=N^(1/α) := by
    rw [show 1/α=1-(1-1/α) by ring,Real.rpow_sub hN,Real.rpow_one]
    rfl
  rw [he,←Real.rpow_mul hN.le]
  field_simp
  rw [Real.rpow_one]

theorem largeGcdThreshold_bounds (α N : ℝ) (hα1 : 1≤α) (hα2 : α≤2) (hN : 4≤N) :
    1≤largeGcdThreshold α N ∧ largeGcdThreshold α N≤N/2 := by
  have hα : 0<α := by linarith
  have hN0 : 0<N := by linarith
  have ha : 0≤1-1/α := by
    have hi : 1/α≤1 := (div_le_one hα).mpr hα1
    linarith
  have hb : 1-1/α≤(1/2:ℝ) := by
    have hi : (1/2:ℝ)≤1/α := (le_div_iff₀ hα).mpr (by linarith)
    linarith
  refine ⟨Real.one_le_rpow (by linarith) ha,?_⟩
  calc
    largeGcdThreshold α N ≤ N^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hb
    _ = Real.sqrt N := (Real.sqrt_eq_rpow N).symm
    _ ≤ N/2 := (Real.sqrt_le_iff).mpr ⟨by positivity,by nlinarith⟩

theorem high_kernel_chosen_scale (M N K : ℝ) (hM : 0<M) (_hN : 0<N) (hK : 0<K)
    (hcut : N^2/M≤K) : Real.sqrt ((2*M)/K)*N≤2*M := by
  have hNK : N^2≤M*K := by
    have h := (div_le_iff₀ hM).mp hcut
    nlinarith
  let s := Real.sqrt ((2*M)/K)
  have hs0 : 0≤s := Real.sqrt_nonneg _
  have hs : s^2*K=2*M := by
    dsimp only [s]
    rw [Real.sq_sqrt (by positivity),div_mul_cancel₀ _ hK.ne']
  have hb : s^2*N^2≤2*M^2 := by
    calc
      _ ≤ s^2*(M*K) := mul_le_mul_of_nonneg_left hNK (sq_nonneg s)
      _ = (s^2*K)*M := by ring
      _ = _ := by rw [hs]; ring
  change s*N≤2*M
  nlinarith [sq_nonneg (s*N)]

theorem chosen_large_gcd_main (α M N K : ℝ) (hα : α≠0)
    (hM : 0<M) (hN : 0<N) (hK : 0<K) (hcut : N^2/M≤K) :
    2*M+Real.sqrt ((2*M)/K)*(N/largeGcdThreshold α N)^α≤4*M := by
  rw [largeGcdThreshold_quotient_power α N hα hN]
  linarith [high_kernel_chosen_scale M N K hM hN hK hcut]

theorem chosen_large_gcd_full (α deltaLoss C M N K : ℝ) (hα1 : 1≤α) (hα2 : α≤2)
    (hδ : 0≤deltaLoss) (hC : 0≤C) (hM : 0<M) (hN : 4≤N) (hK : 0<K)
    (hcut : N^2/M≤K) :
    C*((2*M)*(N/largeGcdThreshold α N))^deltaLoss*
      (2*M+Real.sqrt ((2*M)/K)*(N/largeGcdThreshold α N)^α) ≤
        (4*C*2^deltaLoss)*(M*N)^deltaLoss*M := by
  have hh := largeGcdThreshold_bounds α N hα1 hα2 hN
  have hH : 0<largeGcdThreshold α N := by linarith
  have hN0 : 0<N := by linarith
  have hp : ((2*M)*(N/largeGcdThreshold α N))^deltaLoss≤(2*(M*N))^deltaLoss := by
    apply Real.rpow_le_rpow (by positivity) _ hδ
    have hn := div_le_self hN0.le hh.1
    nlinarith
  have hm := chosen_large_gcd_main α M N K (by linarith) hM hN0 hK hcut
  calc
    _ ≤ C*(2*(M*N))^deltaLoss*(4*M) := by gcongr
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (by positivity)]; ring

end CanonicalQuadraticSieve

end

end OAI

end


