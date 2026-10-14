-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0139_parallel1
-- name    : PNT_ZeroFree_433_0139_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:47:38.273105+00:00
-- url     : https://prove2.me/theorems/ed12551f-17ab-4f28-8f3b-8ee733fa920e
-- title:
--   Zero-free region foundations: QuadraticSieve.LogarithmicLoss [0139_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.LogarithmicLoss
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/LogarithmicLoss.lean#L76-L555

import Definitions.Def_PNT_ZeroFree_433_0052
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0065_1
import Definitions.Def_PNT_ZeroFree_433_0103
import Definitions.Def_PNT_ZeroFree_433_0110
import Definitions.Def_PNT_ZeroFree_433_0118_parallel1
import Definitions.Def_PNT_ZeroFree_433_0122_parallel1
import Definitions.Def_PNT_ZeroFree_433_0124_parallel1
import Definitions.Def_PNT_ZeroFree_433_0127_parallel2
import Definitions.Def_PNT_ZeroFree_433_0128_parallel1
import Definitions.Def_PNT_ZeroFree_433_0129_parallel1
import Definitions.Def_PNT_ZeroFree_433_0130_parallel1
import Definitions.Def_PNT_ZeroFree_433_0135_parallel1
import Definitions.Def_PNT_ZeroFree_433_0137_parallel1
import Definitions.Def_PNT_ZeroFree_433_0137_parallel2
import Definitions.Def_PNT_ZeroFree_433_0138_parallel1
import Definitions.Def_PNT_ZeroFree_433_0181_parallel1
import Definitions.Def_PNT_ZeroFree_433_0208_parallel1
import Definitions.Def_PNT_ZeroFree_433_0264_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/LogarithmicLoss.lean
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
open scoped BigOperators

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

theorem lifting_annular_scale_bounds (j : Fin 7) : 1≤(2:ℝ)^j.val ∧ (2:ℝ)^j.val≤64 := by
  refine ⟨one_le_pow₀ (by norm_num),?_⟩
  have hj : j.val≤6 := by omega
  have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hj
  norm_num at hh
  exact hh


theorem HasSieveExponent.low_threshold {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1≤α) (hα2 : α≤2) (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (c : ℝ) (hc : 4≤c) :
    ∃ C : ℝ, 0<C ∧ ∀ M N : ℝ, 1≤M → 1≤N → N^(2-1/α)≤M → M≤N^2 →
      sieveNorm (selectedPoissonK c M N η) N≤C*(M*N)^(6*η)*M := by
  obtain ⟨C,hC,hrev⟩ := hexp.reverse η hη
  have hc0 : 0<c := by linarith
  refine ⟨C*c^η*(1+c^α),by positivity,?_⟩
  intro M N hM hN hthreshold hupper
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hP : 1≤M*N := by nlinarith
  have hP0 : 0<M*N := by positivity
  have hNM := improved_threshold_ge_column α N M hα hN hthreshold
  have hNP : N≤M*N := by nlinarith
  have hK := (selectedPoisson_bounds c M N η hc hM hN hupper hη.le).2.1
  have hKP := (selectedPoisson_upper c c M N η hc le_rfl hM hN hη.le hη1).2.2
  have hprod : selectedPoissonK c M N η*N≤c*(M*N)^4 := by
    calc
      _ ≤ (c*(M*N)^3)*(M*N) := by gcongr
      _ = _ := by ring
  have hsmall : (selectedPoissonK c M N η*N)^η≤c^η*(M*N)^(4*η) := by
    calc
      _ ≤ (c*(M*N)^4)^η := Real.rpow_le_rpow (by positivity) hprod hη.le
      _ = _ := by
        rw [Real.mul_rpow hc0.le (by positivity)]
        congr 1
        rw [←Real.rpow_natCast,←Real.rpow_mul hP0.le]
        norm_num
  have hmain : (selectedPoissonK c M N η)^α≤c^α*(M*N)^(2*η)*M := by
    apply (improved_threshold_low α c η N M (by linarith) hc0 hN0 hM0 hthreshold).trans
    have hp : (M*N)^(η*α)≤(M*N)^(2*η) := Real.rpow_le_rpow_of_exponent_le hP (by nlinarith)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hc0.le _))
      hNM hN0.le (by positivity)
  have hR : 1≤(M*N)^(2*η) := Real.one_le_rpow hP (by positivity)
  have hsum : N+(selectedPoissonK c M N η)^α≤(1+c^α)*(M*N)^(2*η)*M := by
    calc
      _ ≤ M+c^α*(M*N)^(2*η)*M := add_le_add hNM hmain
      _ ≤ (M*N)^(2*η)*M+c^α*(M*N)^(2*η)*M := by
        exact add_le_add (le_mul_of_one_le_left hM0.le hR) le_rfl
      _ = _ := by ring
  have hpowers : (M*N)^(4*η)*(M*N)^(2*η)=(M*N)^(6*η) := by
    rw [←Real.rpow_add hP0]
    congr 1
    ring
  calc
    _ ≤ C*(selectedPoissonK c M N η*N)^η*(N+(selectedPoissonK c M N η)^α) := hrev _ _ hK hN
    _ ≤ C*(c^η*(M*N)^(4*η))*((1+c^α)*(M*N)^(2*η)*M) := by gcongr
    _ = C*c^η*(1+c^α)*((M*N)^(4*η)*(M*N)^(2*η))*M := by ring
    _ = _ := by rw [hpowers]

end CanonicalQuadraticSieve

open scoped BigOperators Classical
namespace SecondPassArithmetic

theorem globalCutoffRatio_le (K ell B F M H U : ℝ)
    (hU : 1≤U) (hK : 0<K) (hell : 0<ell) (hB : 1≤B) (hF : 1≤F) (hH : 0≤H)
    (hKU : K≤U) (hellU : ell≤U) (hHU : H≤U) (heU : Real.exp M≤U) :
    H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M≤U^8 := by
  have hB0 : 0<B := by linarith
  have hF0 : 0<F := by linarith
  have hden : 1≤B^2*F^2 := by nlinarith [sq_nonneg (B-1),sq_nonneg (F-1)]
  have he : H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M =
      (H*K*ell^2*(Real.exp M)^4)/(B^2*F^2) := by
    unfold globalRowScaleFloor
    field_simp

  rw [he]
  calc
    _ ≤ H*K*ell^2*(Real.exp M)^4 := div_le_self (by positivity) hden
    _ ≤ U*U*U^2*U^4 := by gcongr
    _ = U^8 := by ring

theorem globalNormCaps_polynomial (K ell B F M H U : ℝ)
    (hU : 1≤U) (hK : 0<K) (hell : 0<ell) (hB : 1≤B) (hF : 1≤F) (hH : 0≤H)
    (hKU : K≤U) (hellU : ell≤U) (hBU : B≤U) (hHU : H≤U) (heU : Real.exp M≤U) :
    ∀i, 0<globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H i ∧
      globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H i≤27*U^22 := by
  have hU0 : 0<U := by linarith
  have hB0 : 0<B := by linarith
  have hF0 : 0<F := by linarith
  have hL : ell*Real.exp M≤U^2 := by
    calc
      _ ≤ U*U := mul_le_mul hellU heU (Real.exp_pos M).le hU0.le
      _ = _ := by ring
  have hratio := globalCutoffRatio_le K ell B F M H U hU hK hell hB hF hH hKU hellU hHU heU
  have hY := globalRowScaleFloor_pos K ell B F M hK hell hB0 hF0
  have hratio0 : 0≤H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M := by positivity
  have hceil : (⌈H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M⌉₊:ℝ)+1≤U^8+2 := by
    have hh := Nat.ceil_lt_add_one hratio0
    linarith
  have hpow8 : 1≤U^8 := one_le_pow₀ hU
  have hceil' : (⌈H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M⌉₊:ℝ)+1≤3*U^8 := by linarith
  have hrow : 3*(ell*Real.exp M)^2*B^2*
      ((⌈H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M⌉₊:ℝ)+1)^2≤27*U^22 := by
    calc
      _ ≤ 3*(U^2)^2*U^2*(3*U^8)^2 := by gcongr
      _ = 27*U^22 := by ring
  have hpow2 : U^2≤27*U^22 := by
    calc
      U^2 ≤ U^22 := pow_le_pow_right₀ hU (by omega)
      _ ≤ 27*U^22 := by nlinarith [pow_nonneg hU0.le 22]
  have hpow4 : U^4≤27*U^22 := by
    calc
      U^4 ≤ U^22 := pow_le_pow_right₀ hU (by omega)
      _ ≤ 27*U^22 := by nlinarith [pow_nonneg hU0.le 22]
  have hB2 : B^2≤27*U^22 := (pow_le_pow_left₀ hB0.le hBU 2).trans hpow2
  have hLB : (ell*Real.exp M)*B^2≤27*U^22 := by
    calc
      _ ≤ U^2*U^2 := by gcongr
      _ = U^4 := by ring
      _ ≤ _ := hpow4
  intro i
  fin_cases i
  all_goals first
    | change 0 < ell * Real.exp M ∧ ell * Real.exp M ≤ 27 * U ^ 22
    | change 0 < B ^ 2 ∧ B ^ 2 ≤ 27 * U ^ 22
    | change 0 < (ell * Real.exp M) * B ^ 2 ∧ (ell * Real.exp M) * B ^ 2 ≤ 27 * U ^ 22
    | change 0 < 3 * (ell * Real.exp M) ^ 2 * B ^ 2 *
        ((⌈H * (ell * Real.exp M) ^ 2 / globalRowScaleFloor K ell B F M⌉₊ : ℝ) + 1) ^ 2 ∧
        3 * (ell * Real.exp M) ^ 2 * B ^ 2 *
        ((⌈H * (ell * Real.exp M) ^ 2 / globalRowScaleFloor K ell B F M⌉₊ : ℝ) + 1) ^ 2 ≤ 27 * U ^ 22
  all_goals constructor
  all_goals first | positivity | exact hL.trans hpow2 | exact hB2 | exact hLB | exact hrow

theorem normLogBin_le_log_upper (x Y : ℝ) (hx : 0<x) (hxy : x≤Y) (hY : 1≤Y) :
    (normLogBin x:ℝ)≤Real.log Y := by
  have hh : (normLogBin x:ℝ)≤normLogBin Y := by exact_mod_cast normLogBin_mono hx hxy
  exact hh.trans (Nat.floor_le (Real.log_nonneg hY))

theorem globalLogBox_card_le_log (caps : Fin 10 → ℝ) (Y : ℝ) (hY : 1≤Y)
    (hcaps : ∀i,0<caps i ∧ caps i≤Y) :
    ((globalLogBox caps).card:ℝ)≤(1+Real.log Y)^10 := by
  calc
    ((globalLogBox caps).card:ℝ) = ∏i : Fin 10,((normLogBin (caps i):ℝ)+1) := by
      rw [globalLogBox_card]
      push_cast
      rfl
    _ ≤ ∏_i : Fin 10,(1+Real.log Y) := by
      apply Finset.prod_le_prod (by intro i _; positivity)
      intro i _
      linarith [normLogBin_le_log_upper (caps i) Y (hcaps i).1 (hcaps i).2 hY]
    _ = (1+Real.log Y)^10 := by simp

theorem globalLogBox_card_polynomial_log (K ell B F M H U : ℝ)
    (hU : 1≤U) (hK : 0<K) (hell : 0<ell) (hB : 1≤B) (hF : 1≤F) (hH : 0≤H)
    (hKU : K≤U) (hellU : ell≤U) (hBU : B≤U) (hHU : H≤U) (heU : Real.exp M≤U) :
    ((globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).card:ℝ)≤
      (1+Real.log 27+22*Real.log U)^10 := by
  have hU0 : 0<U := by linarith
  have hY : 1≤27*U^22 := by nlinarith [one_le_pow₀ hU (n:=22)]
  have hh := globalLogBox_card_le_log _ (27*U^22) hY
    (globalNormCaps_polynomial K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU)
  have he : 1+Real.log (27*U^22)=1+Real.log 27+22*Real.log U := by
    rw [Real.log_mul (by norm_num : (27:ℝ)≠0) (pow_ne_zero 22 hU0.ne'),Real.log_pow]
    norm_num
    ring
  rwa [he] at hh

theorem globalLogRep_le_upper (caps : Fin 10 → ℝ) (j : GlobalLogIndex)
    (hj : j∈globalLogBox caps) (i : Fin 10) (Y : ℝ)
    (hc : 0<caps i) (hcap : caps i≤Y) (hY : 1≤Y) : globalLogRep j i≤Y := by
  have hji : j i≤normLogBin (caps i) := by
    have hh := Fintype.mem_piFinset.mp hj i
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hh)
  have hjY := hji.trans (normLogBin_mono hc hcap)
  have hr : globalLogRep j i≤normLogScale (normLogBin Y) := by
    unfold globalLogRep normLogScale
    apply Real.exp_le_exp.mpr
    exact_mod_cast hjY
  exact hr.trans (normLogBin_scale_bounds Y hY).1


end SecondPassArithmetic

namespace CanonicalQuadraticSieve

theorem sieveNorm_small_columns (M N : ℝ) (hM : 1≤M) (hN : 1≤N) (hN28 : N≤28) :
    sieveNorm M N≤785*QuadraticInitialBound.initialSieveConstant*M := by
  have hceil : (⌈N⌉₊:ℝ)≤28 := by
    exact_mod_cast (Nat.ceil_le.mpr hN28 : ⌈N⌉₊≤28)
  have hs : (⌈N⌉₊:ℝ)^2≤784 := by
    nlinarith [Nat.cast_nonneg (α:=ℝ) ⌈N⌉₊]
  have hc := QuadraticInitialBound.initialSieveConstant_pos
  have hb := sieveNorm_initial M N hM hN
  have ht : M+(⌈N⌉₊:ℝ)^2≤785*M := by linarith
  calc
    _ ≤ QuadraticInitialBound.initialSieveConstant*(M+(⌈N⌉₊:ℝ)^2) := hb
    _ ≤ QuadraticInitialBound.initialSieveConstant*(785*M) := mul_le_mul_of_nonneg_left ht hc.le
    _ = _ := by ring


open ActualEisensteinCubic CompletedGauss


end CanonicalQuadraticSieve

namespace SecondPassArithmetic

theorem globalLogFactor_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ U : ℝ, 1≤U →
      (1+Real.log 27+22*Real.log U)^10≤C*U^ε := by
  let deltaLoss := ε/10
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  let C0 := 1+Real.log 27+22/deltaLoss
  have hlog : 0≤Real.log 27 := Real.log_nonneg (by norm_num)
  have hC0 : 0<C0 := by dsimp [C0]; positivity
  refine ⟨C0^10,by positivity,?_⟩
  intro U hU
  have hU0 : 0<U := by linarith
  have hR : 1≤U^deltaLoss := Real.one_le_rpow hU hδ.le
  have hb : Real.log U≤U^deltaLoss/deltaLoss := Real.log_le_rpow_div hU0.le hδ
  have hs : 1+Real.log 27+22*Real.log U≤C0*U^deltaLoss := by
    calc
      _ ≤ (1+Real.log 27)*U^deltaLoss+22*(U^deltaLoss/deltaLoss) := add_le_add
        (le_mul_of_one_le_right (by linarith) hR)
        (mul_le_mul_of_nonneg_left hb (by norm_num))
      _ = C0*U^deltaLoss := by dsimp [C0]; ring
  have hs0 : 0≤1+Real.log 27+22*Real.log U := by
    have hu := Real.log_nonneg hU
    positivity
  calc
    _ ≤ (C0*U^deltaLoss)^10 := pow_le_pow_left₀ hs0 hs 10
    _ = C0^10*U^ε := by
      rw [mul_pow]
      congr 1
      rw [←Real.rpow_natCast,←Real.rpow_mul hU0.le]
      dsimp [deltaLoss]
      congr 1
      ring

theorem globalLogBox_card_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ K ell B F M H U : ℝ,
      1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U →
      ((globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).card:ℝ)≤C*U^ε := by
  obtain ⟨C,hC,hbound⟩ := globalLogFactor_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU
  exact (globalLogBox_card_polynomial_log K ell B F M H U hU hK hell hB hF hH
    hKU hellU hBU hHU heU).trans (hbound U hU)


end SecondPassArithmetic

end

end OAI

end


