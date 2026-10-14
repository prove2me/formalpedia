-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0121_parallel1
-- name    : PNT_ZeroFree_433_0121_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:42:29.349608+00:00
-- url     : https://prove2.me/theorems/bb8cfc80-2e48-45c9-8f0b-012e6299e6b9
-- title:
--   Zero-free region foundations: QuadraticSieve.PrincipalMajorants [0121_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.PrincipalMajorants
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/PrincipalMajorants.lean#L84-L766

import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0060
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0072
import Definitions.Def_PNT_ZeroFree_433_0077
import Definitions.Def_PNT_ZeroFree_433_0082
import Definitions.Def_PNT_ZeroFree_433_0092
import Definitions.Def_PNT_ZeroFree_433_0098
import Definitions.Def_PNT_ZeroFree_433_0103
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0114
import Definitions.Def_PNT_ZeroFree_433_0115
import Definitions.Def_PNT_ZeroFree_433_0118_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0119_parallel1
import Definitions.Def_PNT_ZeroFree_433_0122_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0127_parallel2
import Definitions.Def_PNT_ZeroFree_433_0129_parallel1
import Definitions.Def_PNT_ZeroFree_433_0135_parallel1
import Definitions.Def_PNT_ZeroFree_433_0137_parallel2
import Definitions.Def_PNT_ZeroFree_433_0181_parallel1
import Definitions.Def_PNT_ZeroFree_433_0264_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/PrincipalMajorants.lean
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

open scoped BigOperators Classical SchwartzMap

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open IdealMobiusDivisorSum

def smallPrincipalMajorant {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U : ℝ) (a : n → ℂ) (b : p → ℂ) : ℝ :=
  ((columnDyadicLength N+1:ℕ):ℝ)^2 *
    (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
      (M/F+(2*U)*Real.sqrt (M/F)*B^(α-1/2)))

lemma smallPrincipalMajorant_nonneg {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U : ℝ) (a : n → ℂ) (b : p → ℂ)
    (hB : 0 ≤ B) (hN : 0 ≤ N) (hM : 0 ≤ M) (hF : 0 ≤ F) (hU : 0 ≤ U) :
    0 ≤ smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b := by
  have he := divisorEnergyFactor_nonneg ε hε N a b
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  unfold smallPrincipalMajorant
  positivity

lemma smallPrincipalMajorant_mono {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B' B N M F U : ℝ) (a a' : n → ℂ) (b b' : p → ℂ)
    (hB' : 0 ≤ B') (hB : B' ≤ B) (hN : 0 ≤ N) (hM : 0 ≤ M) (hF : 0 ≤ F) (hU : 0 ≤ U)
    (ha : ∀ j, ‖a' j‖ ≤ ‖a j‖) (hb : ∀ k, ‖b' k‖ ≤ ‖b k‖) :
    smallPrincipalMajorant hexp deltaLoss hδ ε hε B' N M F U a' b' ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b := by
  have he := divisorEnergyFactor_mono_coefficients ε hε N a a' b b' ha hb
  have he0 := divisorEnergyFactor_nonneg ε hε N a' b'
  have he1 := divisorEnergyFactor_nonneg ε hε N a b
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  have ha0 : 0 ≤ α-1/2 := by linarith
  have hB0 : 0 ≤ B := hB'.trans hB
  unfold smallPrincipalMajorant
  gcongr

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def unrestrictedSmallPrincipalSum
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) : ℂ := by
  classical
  exact ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows left right a b i j k *
    ∑ d ∈ idealDivisors (left j*right k), if P d i then
      (UniqueFactorizationMonoid.moebius d:ℂ)*
        ((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ) else 0


end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem weightedDivisorCorrection_coprime_mask (G C : Ideal O)
    (hG : G ≠ 0) (hC : C ≠ 0) (hGC : IsCoprime G C) (X Z : ℝ) :
    (∑ d ∈ idealDivisors (G*C), if Z < (Ideal.absNorm d:ℝ) then
      (UniqueFactorizationMonoid.moebius d:ℂ)*((X/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0) =
    ∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
      ∑ d ∈ idealDivisors C, if Z/(Ideal.absNorm q:ℝ) < (Ideal.absNorm d:ℝ) then
        (UniqueFactorizationMonoid.moebius d:ℂ)*(((X/(Ideal.absNorm q:ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0 := by
  classical
  rw [QuadraticDivisorSplit.sum_divisors_coprime_product G C hG hC hGC]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hqG := (mem_idealDivisors hG).mp hq
  have hdC := (mem_idealDivisors hC).mp hd
  have hq0 : q ≠ 0 := by intro he; rw [he,zero_dvd_iff] at hqG; exact hG hqG
  have hNq : 0 < (Ideal.absNorm q:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun he => hq0 (Ideal.absNorm_eq_zero_iff.mp he))
  have hlow : Z < (Ideal.absNorm q:ℝ)*(Ideal.absNorm d:ℝ) ↔
      Z/(Ideal.absNorm q:ℝ) < (Ideal.absNorm d:ℝ) := by
    constructor
    · intro hz
      apply (div_lt_iff₀ hNq).mpr
      simpa only [mul_comm] using hz
    · intro hz
      simpa only [mul_comm] using (div_lt_iff₀ hNq).mp hz
  simp only [map_mul,Nat.cast_mul,hlow,(hGC.mono hqG hdC).isRelPrime.moebius_mul,Int.cast_mul]
  by_cases hp : Z/(Ideal.absNorm q:ℝ) < (Ideal.absNorm d:ℝ)
  · simp only [hp,ite_true]
    push_cast
    ring
  · simp only [hp,ite_false,mul_zero]

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def maskedPrincipalDivisorCorrection (G : Ideal O)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Z : m → ℝ) : ℂ := by
  classical
  exact ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    ∑ d ∈ idealDivisors (G*(left j*right k)), if Z i < (Ideal.absNorm d:ℝ) then
      (UniqueFactorizationMonoid.moebius d:ℂ)*
        ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem maskedPrincipalDivisorCorrection_eq
    (G : Ideal O) (hG : G ≠ 0)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (hM : 0 ≤ M) (Z : m → ℝ)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hGl : ∀ j, IsCoprime G (left j)) (hGr : ∀ k, IsCoprime G (right k)) :
    maskedPrincipalDivisorCorrection G rows left right a b M Z =
      ∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
        principalDivisorCorrection rows left right a b (M/(Ideal.absNorm q:ℝ)^2)
          (fun d i => Z i/(Ideal.absNorm q:ℝ) < (Ideal.absNorm d:ℝ)) := by
  classical
  have ht (i : m) (j : n) (k : p) :
      (∑ d ∈ idealDivisors (G*(left j*right k)), if Z i < (Ideal.absNorm d:ℝ) then
        (UniqueFactorizationMonoid.moebius d:ℂ)*
          ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0) =
      ∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
        ∑ d ∈ idealDivisors (left j*right k), if Z i/(Ideal.absNorm q:ℝ) < (Ideal.absNorm d:ℝ) then
          (UniqueFactorizationMonoid.moebius d:ℂ)*
            ((Real.sqrt ((M/(Ideal.absNorm q:ℝ)^2)/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0 := by
    rw [weightedDivisorCorrection_coprime_mask G _ hG (mul_ne_zero (hleft j) (hright k))
      ((hGl j).mul_right (hGr k))]
    apply Finset.sum_congr rfl
    intro q hq
    have hqG := (mem_idealDivisors hG).mp hq
    have hq0 : q ≠ 0 := by intro he; rw [he,zero_dvd_iff] at hqG; exact hG hqG
    have hNq : 0 < (Ideal.absNorm q:ℝ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun he => hq0 (Ideal.absNorm_eq_zero_iff.mp he))
    rw [sqrt_norm_divisor_scale M _ _ hM (Nat.cast_nonneg _) hNq]
  unfold maskedPrincipalDivisorCorrection
  simp_rw [ht,Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ:Finset p)) (t := idealDivisors G),
    Finset.sum_comm (s := (Finset.univ:Finset n)) (t := idealDivisors G),
    Finset.sum_comm (s := (Finset.univ:Finset m)) (t := idealDivisors G)]
  simp only [principalDivisorCorrection,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring_nf


end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open IdealMobiusDivisorSum

lemma smallPrincipalMajorant_bad_scale {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U Q : ℝ) (a a' : n → ℂ) (b b' : p → ℂ)
    (hB : 0 ≤ B) (hN : 0 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U) (hQ : 1 ≤ Q)
    (ha : ∀ j, ‖a' j‖ ≤ ‖a j‖) (hb : ∀ k, ‖b' k‖ ≤ ‖b k‖) :
    (1/Q)*smallPrincipalMajorant hexp deltaLoss hδ ε hε (B/Q) N (M*Q) F U a' b' ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b := by
  have hQp : 0 < Q := by linarith
  have he := divisorEnergyFactor_mono_coefficients ε hε N a a' b b' ha hb
  have hp : ((B/Q)*N)^deltaLoss ≤ (B*N)^deltaLoss := by
    apply Real.rpow_le_rpow (by positivity) _ hδ.le
    exact mul_le_mul_of_nonneg_right (div_le_self hB hQ) hN
  have hs := dual_bad_sector_scale M F B Q U α hM hF hB hQ hU hα
  have he0 := divisorEnergyFactor_nonneg ε hε N a' b'
  have he1 := divisorEnergyFactor_nonneg ε hε N a b
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  unfold smallPrincipalMajorant
  calc
    _ = ((columnDyadicLength N+1:ℕ):ℝ)^2 *
      (2*divisorEnergyFactor ε hε N a' b'*(divisorExponentConstant hexp deltaLoss hδ*((B/Q)*N)^deltaLoss)*
        ((1/Q)*(M*Q/F+(2*U)*Real.sqrt (M*Q/F)*(B/Q)^(α-1/2)))) := by ring
    _ ≤ _ := by gcongr

lemma sqrt_sector_scale (M F Q b : ℝ) (hM : 0 < M) (hF : 0 < F) (hQ : 0 < Q) (hb : 0 < b) :
    Real.sqrt ((M/F)/(Q*b)) = (1/Q)*Real.sqrt (((M*Q)/F)/b) := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt (show 0 ≤ (M/F)/(Q*b) by positivity),
    Real.sq_sqrt (show 0 ≤ ((M*Q)/F)/b by positivity)]
  field_simp

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def unrestrictedLargePrincipalSum
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Z : m → ℝ) : ℂ := by
  classical
  exact ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows left right a b i j k *
    ∑ d ∈ idealDivisors (left j*right k), if Z i < (Ideal.absNorm d:ℝ) then
      (UniqueFactorizationMonoid.moebius d:ℂ)*
        ((Real.sqrt ((M/F)/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma unrestrictedLargePrincipalSum_sector
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Z : m → ℝ) (hM : 0 < M) (hF : 0 < F)
    (hrows : ∀ i, Squarefree (rows i)) (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E) (hQ : sectorBadIdeal E ≠ 0) :
    unrestrictedLargePrincipalSum rows left right a b M F Z =
      ((1/(Ideal.absNorm (sectorBadIdeal E):ℝ):ℝ):ℂ)*
        principalDivisorCorrection (fun i => goodSquarefreePart (rows i)) left right
          (fun j => a j*quadraticRow (left j) (idealGenerator (sectorBadIdeal E)))
          (fun k => b k*quadraticRow (right k) (idealGenerator (sectorBadIdeal E)))
          ((M*(Ideal.absNorm (sectorBadIdeal E):ℝ))/F) (fun d i => Z i < (Ideal.absNorm d:ℝ)) := by
  classical
  have hQp : 0 < (Ideal.absNorm (sectorBadIdeal E):ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hQ (Ideal.absNorm_eq_zero_iff.mp h))
  unfold unrestrictedLargePrincipalSum principalDivisorCorrection
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [unrestrictedPairTerm_sector rows left right a b hrows hleft hright hray E hE i j k]
  have hn : (Ideal.absNorm (rows i):ℝ) =
      (Ideal.absNorm (sectorBadIdeal E):ℝ)*(Ideal.absNorm (goodSquarefreePart (rows i)):ℝ) := by
    have hi := congrArg (fun I : Ideal O => (Ideal.absNorm I:ℝ))
      (sector_bad_good_product (rows i) (hrows i) E (hE i))
    simpa only [map_mul,Nat.cast_mul] using hi.symm
  have hgpos : 0 < (Ideal.absNorm (goodSquarefreePart (rows i)):ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h =>
      (goodSquarefreePart_admissible (rows i)).1 (Ideal.absNorm_eq_zero_iff.mp h))
  rw [hn,sqrt_sector_scale M F _ _ hM hF hQp hgpos]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : Z i < (Ideal.absNorm d:ℝ)
  · simp only [hd,ite_true,Complex.ofReal_div,Complex.ofReal_mul]
    ring
  · simp only [hd,ite_false,mul_zero]


end

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

lemma unrestrictedPairTerm_norm_le {m n p : Type}
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (i : m) (j : n) (k : p) :
    ‖unrestrictedPairTerm rows left right a b i j k‖ ≤ ‖a j‖*‖b k‖ := by
  classical
  unfold unrestrictedPairTerm
  split_ifs with hc
  · simp only [unrestrictedPairCharacter,norm_mul,norm_star]
    calc
      _ ≤ (‖a j‖*‖b k‖)*(1*1) := mul_le_mul_of_nonneg_left
        (mul_le_mul (quadraticRow_norm_le_one _ _) (quadraticRow_norm_le_one _ _)
          (norm_nonneg _) (by norm_num)) (by positivity)
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

theorem unrestricted_pair_error_energy {m n : Type} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ)
    (E : ℝ) (hE : 0 ≤ E) (error : m → n → n → ℂ)
    (herr : ∀ i j k, ‖error i j k‖ ≤ E) :
    ‖∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows cols cols a a i j k * error i j k‖ ≤
      Fintype.card m * Fintype.card n * E * ∑ j, ‖a j‖ ^ 2 := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j : n => ‖a j‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hcs
  have hs : (∑ j, ∑ k, ‖a j‖ * ‖a k‖ * E) = (∑ j, ‖a j‖) ^ 2 * E := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  calc
    _ ≤ ∑ i, ∑ j, ∑ k, ‖unrestrictedPairTerm rows cols cols a a i j k * error i j k‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun j hj => norm_sum_le _ _)
    _ ≤ ∑ _i : m, ∑ j, ∑ k, ‖a j‖ * ‖a k‖ * E := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul]
      exact mul_le_mul (unrestrictedPairTerm_norm_le rows cols cols a a i j k) (herr i j k)
        (norm_nonneg _) (by positivity)
    _ = (Fintype.card m : ℝ) * ((∑ j, ‖a j‖) ^ 2 * E) := by
      simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Fintype.card m : ℝ) * (((∑ j, ‖a j‖ ^ 2) * Fintype.card n) * E) := by gcongr
    _ = _ := by ring

theorem unrestricted_pair_error_ideal_bound {m n : Type} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (hr : Function.Injective rows) (hc : Function.Injective cols)
    (B N : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hrows : ∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (hcols : ∀ j, cols j ≠ 0 ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (a : n → ℂ) (E : ℝ) (hE : 0 ≤ E) (error : m → n → n → ℂ)
    (herr : ∀ i j k, ‖error i j k‖ ≤ E) :
    ‖∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows cols cols a a i j k * error i j k‖ ≤
      16384 * B * N * E * ∑ j, ‖a j‖ ^ 2 := by
  have hrc := finite_ideal_family_card_bound rows hr B hB (fun i => (hrows i).1) (fun i => (hrows i).2)
  have hcc := finite_ideal_family_card_bound cols hc N hN (fun j => (hcols j).1) (fun j => (hcols j).2)
  apply (unrestricted_pair_error_energy rows cols a E hE error herr).trans
  calc
    _ ≤ (128 * B) * (128 * N) * E * ∑ j, ‖a j‖ ^ 2 := by gcongr
    _ = _ := by ring

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
def unrestrictedDualPrincipalErrorSum (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M F N T : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows cols cols a a i j k *
    (((M / (Real.sqrt ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) * F) : ℝ) : ℂ) *
      truncationError (fun P : primePool {cols j * cols k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))))
        ((N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))) / T)
        (T * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) (T ^ 4))

omit [DecidableEq m] [DecidableEq n] in
theorem unrestrictedDualPrincipal_actual_error_sum_bound (l : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (B N M F T : ℝ),
        1 ≤ B → 1 ≤ N → 0 < M → 0 < F → 4 ≤ T →
        ∀ (rows : m → Ideal O) (cols : n → Ideal O),
          Function.Injective rows → Function.Injective cols →
          (∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B) →
          (∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) →
          ∀ (a : n → ℂ) (W : 𝓢(ℝ, ℂ)),
          ‖unrestrictedDualPrincipalErrorSum rows cols a W M F N T‖ ≤
            16384 * B * N *
              ((2 * M / (F * N)) * ((supportConstant ε hε * (N * N) ^ ε) *
                (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ l)) *
              ∑ j, ‖a j‖ ^ 2 := by
  obtain ⟨s, C, hC, hb⟩ := primePool_symmetric_error_bound l
  refine ⟨s, C, hC, ?_⟩
  intro ε hε B N M F T hB hN hM hF hT rows cols hr hc hrows hcols a W
  let E₀ := (supportConstant ε hε * (N * N) ^ ε) *
    (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ l
  let error : m → n → n → ℂ := fun i j k =>
    (((M / (Real.sqrt ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) * F) : ℝ) : ℂ) *
      truncationError (fun P : primePool {cols j * cols k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))))
        ((N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))) / T)
        (T * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) (T ^ 4))
  have hsc := (supportConstant_pos ε hε).le
  have hE₀ : 0 ≤ E₀ := by dsimp only [E₀]; positivity
  have herr (i : m) (j k : n) : ‖error i j k‖ ≤ (2 * M / (F * N)) * E₀ := by
    have hi : 0 < (Ideal.absNorm (rows i) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h => (hrows i).1 (Ideal.absNorm_eq_zero_iff.mp h))
    obtain ⟨hX₀, hlo, hhi⟩ := dual_truncation_reference_bounds M F (Ideal.absNorm (rows i)) N
      (Ideal.absNorm (cols j)) (Ideal.absNorm (cols k)) hM hF hi (by linarith) (hcols j).2 (hcols k).2
    have hh := hb ε hε (cols j * cols k) (mul_ne_zero (hcols j).1.1 (hcols k).1.1) W
      _ _ T hX₀ hlo hhi hT
    simp only [map_mul, Nat.cast_mul] at hh
    have he : ‖truncationError (fun P : primePool {cols j * cols k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))))
        ((N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))) / T)
        (T * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) (T ^ 4)‖ ≤ E₀ := by
      apply hh.trans
      dsimp only [E₀]
      gcongr
      · exact (hcols j).2.2
      · exact (hcols k).2.2
    dsimp only [error]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul
      (dual_truncation_prefactor_bound M F N (Ideal.absNorm (cols j)) (Ideal.absNorm (cols k))
        hM hF (by linarith) (hcols j).2 (hcols k).2) he (norm_nonneg _) (by positivity)
  exact unrestricted_pair_error_ideal_bound rows cols hr hc B N hB hN hrows
    (fun j => ⟨(hcols j).1.1, (hcols j).2.2⟩) a _ (by positivity) error herr

end CanonicalQuadraticSieve

end

end OAI

end


