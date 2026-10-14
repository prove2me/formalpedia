-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0118_parallel1_1
-- name    : PNT_ZeroFree_433_0118_parallel1_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:38:07.615308+00:00
-- url     : https://prove2.me/theorems/4504f601-c855-425f-aa43-259ad6d9dbdf
-- title:
--   Zero-free region foundations: Eisenstein.SeedDefects [0118_parallel1_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.SeedDefects
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/SeedDefects.lean#L158-L447

import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0051
import Definitions.Def_PNT_ZeroFree_433_0054
import Definitions.Def_PNT_ZeroFree_433_0054_1
import Definitions.Def_PNT_ZeroFree_433_0059
import Definitions.Def_PNT_ZeroFree_433_0060
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0072
import Definitions.Def_PNT_ZeroFree_433_0073
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0077
import Definitions.Def_PNT_ZeroFree_433_0078
import Definitions.Def_PNT_ZeroFree_433_0079_1
import Definitions.Def_PNT_ZeroFree_433_0080
import Definitions.Def_PNT_ZeroFree_433_0082
import Definitions.Def_PNT_ZeroFree_433_0087
import Definitions.Def_PNT_ZeroFree_433_0089
import Definitions.Def_PNT_ZeroFree_433_0092
import Definitions.Def_PNT_ZeroFree_433_0098
import Definitions.Def_PNT_ZeroFree_433_0101
import Definitions.Def_PNT_ZeroFree_433_0102
import Definitions.Def_PNT_ZeroFree_433_0103
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0107
import Definitions.Def_PNT_ZeroFree_433_0110
import Definitions.Def_PNT_ZeroFree_433_0113
import Definitions.Def_PNT_ZeroFree_433_0114
import Definitions.Def_PNT_ZeroFree_433_0148
import Definitions.Def_PNT_ZeroFree_433_0173_parallel1
import Definitions.Def_PNT_ZeroFree_433_0241
import Definitions.Def_PNT_ZeroFree_433_0242_parallel2
import Definitions.Def_PNT_ZeroFree_433_0260_parallel2
import Definitions.Def_PNT_ZeroFree_433_0265_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0274_parallel1
import Definitions.Def_PNT_ZeroFree_433_0275_parallel1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/SeedDefects.lean
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

namespace CubicEisenstein
open Filter
open scoped BigOperators Classical Topology ContDiff


lemma cuspCutoffCorrection_parameter_entire (F : ℂ → ℝ → ℂ)
    (hF : ∀v,Differentiable ℂ (fun s => F s v)) (w : HyperbolicSpace) :
    Differentiable ℂ (fun s => cuspCutoffCorrection 1 (F s) w) := by
  let S := (high_cosets_finite 1 le_rfl w).toFinset
  have heq : (fun s => cuspCutoffCorrection 1 (F s) w)=
      (fun s => ∑r∈S,cuspCutoffTerm 1 (F s) r w) := by
    funext s
    apply tsum_eq_sum
    intro r hr
    have hh : ¬1<cosetHeight r w := by simpa only [S,Set.Finite.mem_toFinset,Set.mem_ofPred_eq] using hr
    simp [cuspCutoffTerm,hh]
  rw [heq]
  apply Differentiable.fun_sum
  intro r hr
  unfold cuspCutoffTerm
  split_ifs
  · exact (differentiable_const _).mul (hF _)
  · exact differentiable_const _


end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

def sectorBadIdeal (E : fixedBadPrimes.powerset) : Ideal O := ∏ P ∈ E.val, P

theorem sector_bad_good_product (I : Ideal O) (hI : Squarefree I)
    (E : fixedBadPrimes.powerset) (hE : badPrimeSector I = E) :
    sectorBadIdeal E * goodSquarefreePart I = I := by
  have hs : badPrimeSupport I = E.val := congrArg Subtype.val hE
  simpa only [hs, sectorBadIdeal] using squarefree_bad_good_product I hI

theorem sectorBadIdeal_ne_zero_of_row (I : Ideal O) (hI : Squarefree I)
    (E : fixedBadPrimes.powerset) (hE : badPrimeSector I = E) : sectorBadIdeal E ≠ 0 := by
  intro hz
  have hp := sector_bad_good_product I hI E hE
  rw [hz, zero_mul] at hp
  exact hI.ne_zero hp.symm

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def unrestrictedPairTerm (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (i : m) (j : n) (k : p) : ℂ :=
  if IsCoprime (left j) (right k) then
    star (a j) * b k * unrestrictedPairCharacter (left j) (right k) (rows i) else 0

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem unrestrictedPairTerm_sector (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ)
    (hrows : ∀ i, Squarefree (rows i)) (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E) (i : m) (j : n) (k : p) :
    unrestrictedPairTerm rows left right a b i j k =
      originalTerm (fun i => goodSquarefreePart (rows i)) left right
        (fun j => a j * quadraticRow (left j) (idealGenerator (sectorBadIdeal E)))
        (fun k => b k * quadraticRow (right k) (idealGenerator (sectorBadIdeal E))) 1 1 i j k := by
  classical
  by_cases hc : IsCoprime (left j) (right k)
  · simp only [unrestrictedPairTerm, originalTerm, hc, ite_true, one_dvd]
    have hp := unrestrictedPairCharacter_squarefree_bad_split (left j) (right k) (rows i)
      (hleft j) (hright k) (hray j k) (hrows i)
    have hs : badPrimeSupport (rows i) = E.val := congrArg Subtype.val (hE i)
    rw [hp, hs]
    simp only [sectorBadIdeal, unrestrictedPairCharacter, star_mul,
      canonical_quadraticRow_star _ (hleft j)]
    ring
  · simp only [unrestrictedPairTerm, originalTerm, hc, ite_false]

def unrestrictedDualTruncatedMiddle (W : 𝓢(ℝ, ℂ))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows left right a b i j k *
    (((M / (Real.sqrt ((Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ)) * F) : ℝ) : ℂ) *
      middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ)))) (Y i) (Z i) lengthScale)

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem unrestrictedDualTruncatedMiddle_sector
    (W : 𝓢(ℝ, ℂ)) (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hrows : ∀ i, Squarefree (rows i)) (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E)
    (hQ : sectorBadIdeal E ≠ 0) :
    unrestrictedDualTruncatedMiddle W rows left right a b M F Y Z lengthScale =
      ((1 / (Ideal.absNorm (sectorBadIdeal E) : ℝ) : ℝ) : ℂ) *
        dualTruncatedMiddle W (fun i => goodSquarefreePart (rows i)) left right
          (fun j => a j * quadraticRow (left j) (idealGenerator (sectorBadIdeal E)))
          (fun k => b k * quadraticRow (right k) (idealGenerator (sectorBadIdeal E)))
          (M * (Ideal.absNorm (sectorBadIdeal E) : ℝ)) F Y Z lengthScale := by
  classical
  have hQn : (Ideal.absNorm (sectorBadIdeal E) : ℝ) ≠ 0 := by
    exact_mod_cast (show Ideal.absNorm (sectorBadIdeal E) ≠ 0 from fun h => hQ (Ideal.absNorm_eq_zero_iff.mp h))
  unfold unrestrictedDualTruncatedMiddle dualTruncatedMiddle
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [unrestrictedPairTerm_sector rows left right a b hrows hleft hright hray E hE i j k]
  have hn : (Ideal.absNorm (rows i) : ℝ) =
      (Ideal.absNorm (sectorBadIdeal E) : ℝ) * (Ideal.absNorm (goodSquarefreePart (rows i)) : ℝ) := by
    calc
      (Ideal.absNorm (rows i) : ℝ) =
          (Ideal.absNorm (sectorBadIdeal E * goodSquarefreePart (rows i)) : ℝ) :=
        congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ))
          (sector_bad_good_product (rows i) (hrows i) E (hE i)).symm
      _ = _ := by rw [map_mul, Nat.cast_mul]
  rw [hn]
  have harg : F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
      (M * ((Ideal.absNorm (sectorBadIdeal E) : ℝ) * (Ideal.absNorm (goodSquarefreePart (rows i)) : ℝ))) =
    F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
      ((M * (Ideal.absNorm (sectorBadIdeal E) : ℝ)) * (Ideal.absNorm (goodSquarefreePart (rows i)) : ℝ)) := by ring
  rw [harg]
  have hs : (M / (Real.sqrt ((Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ)) * F) : ℝ) =
      (1 / (Ideal.absNorm (sectorBadIdeal E) : ℝ)) *
        ((M * (Ideal.absNorm (sectorBadIdeal E) : ℝ)) /
          (Real.sqrt ((Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ)) * F)) := by
    field_simp [hQn]
  rw [hs, Complex.ofReal_mul]
  ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss

lemma divisorEnergyFactor_mono_coefficients {n p : Type*} [Fintype n] [Fintype p]
    (ε : ℝ) (hε : 0 < ε) (N : ℝ) (a a' : n → ℂ) (b b' : p → ℂ)
    (ha : ∀ j, ‖a' j‖ ≤ ‖a j‖) (hb : ∀ k, ‖b' k‖ ≤ ‖b k‖) :
    divisorEnergyFactor ε hε N a' b' ≤ divisorEnergyFactor ε hε N a b := by
  have hA : (∑ j, ‖a' j‖ ^ 2) ≤ ∑ j, ‖a j‖ ^ 2 :=
    Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (ha j) _)
  have hB : (∑ k, ‖b' k‖ ^ 2) ≤ ∑ k, ‖b k‖ ^ 2 :=
    Finset.sum_le_sum (fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hb k) _)
  have hs := (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le
  have hd := (DivisorBlockCauchy.divisorConstant_pos ε hε).le
  unfold divisorEnergyFactor
  gcongr

lemma dual_bad_sector_scale (M F B Q U α : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 ≤ B) (hQ : 1 ≤ Q)
    (hU : 0 ≤ U) (hα : 1 / 2 ≤ α) :
    (1 / Q) * (M * Q / F + (2 * U) * Real.sqrt (M * Q / F) * (B / Q) ^ (α - 1 / 2)) ≤
      M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2) := by
  have hQp : 0 < Q := by linarith
  have hpow : (B / Q) ^ (α - 1 / 2) ≤ B ^ (α - 1 / 2) :=
    Real.rpow_le_rpow (by positivity) (div_le_self hB hQ) (by linarith)
  have hsQ : Real.sqrt Q ≤ Q := Real.sqrt_le_self_iff.mpr (Or.inr hQ)
  have hs : (1 / Q) * Real.sqrt (M * Q / F) ≤ Real.sqrt (M / F) := by
    have he : M * Q / F = (M / F) * Q := by ring
    rw [he, Real.sqrt_mul (by positivity)]
    have ht : Real.sqrt Q / Q ≤ 1 := (div_le_one hQp).mpr hsQ
    calc
      _ = Real.sqrt (M / F) * (Real.sqrt Q / Q) := by ring
      _ ≤ Real.sqrt (M / F) * 1 := mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg _)
      _ = _ := mul_one _
  calc
    _ = M / F + (2 * U) * ((1 / Q) * Real.sqrt (M * Q / F)) * (B / Q) ^ (α - 1 / 2) := by
      field_simp

    _ ≤ _ := by gcongr

def dualMiddleMajorant {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U : ℝ) (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) : ℝ :=
  ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
    ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
      divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
        (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2)))

lemma dualMiddleMajorant_nonneg {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U : ℝ) (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ))
    (hB : 0 ≤ B) (hN : 0 ≤ N) (hM : 0 ≤ M) (hF : 0 ≤ F) (hU : 0 ≤ U) :
    0 ≤ dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W := by
  have hc := nonzeroLatticeEnvelopeConstant_nonneg
  have hW := dualMiddleDecayConstant_nonneg W
  have he := divisorEnergyFactor_nonneg ε hε N a b
  have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  unfold dualMiddleMajorant
  positivity

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem HasSieveExponent.dual_truncated_middle_sector {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1 / 2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Squarefree (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (hZ : ∀ i, Z i ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E) :
    ‖unrestrictedDualTruncatedMiddle W rows left right a b M F Y Z lengthScale‖ ≤
      dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W := by
  classical
  cases isEmpty_or_nonempty m with
  | inl hempty =>
    let := hempty
    simp only [unrestrictedDualTruncatedMiddle, Finset.univ_eq_empty, Finset.sum_empty, norm_zero]
    exact dualMiddleMajorant_nonneg hexp deltaLoss hδ ε hε B N M F U a b W (by linarith) (by linarith) hM.le hF.le hU
  | inr hnonempty =>
    let := hnonempty
    let i₀ : m := Classical.choice hnonempty
    let Q : ℝ := Ideal.absNorm (sectorBadIdeal E)
    let good := fun i => goodSquarefreePart (rows i)
    let a' := fun j => a j * quadraticRow (left j) (idealGenerator (sectorBadIdeal E))
    let b' := fun k => b k * quadraticRow (right k) (idealGenerator (sectorBadIdeal E))
    have hQnz := sectorBadIdeal_ne_zero_of_row (rows i₀) (hrows i₀).1 E (hE i₀)
    have hQ : 1 ≤ Q := by
      dsimp only [Q]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun h => hQnz (Ideal.absNorm_eq_zero_iff.mp h)))
    have hQp : 0 < Q := by linarith
    have hn (i : m) : (Ideal.absNorm (rows i) : ℝ) = Q * (Ideal.absNorm (good i) : ℝ) := by
      have hi := congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ))
        (sector_bad_good_product (rows i) (hrows i).1 E (hE i))
      simpa only [map_mul, Nat.cast_mul] using hi.symm
    have hgr : Function.Injective good := by
      intro i k h
      exact hr (goodSquarefreePart_injective_on_sector _ _ (hrows i).1 (hrows k).1
        ((hE i).trans (hE k).symm) h)
    have hg (i : m) : Admissible (good i) ∧ (B / Q) / 2 ≤ (Ideal.absNorm (good i) : ℝ) ∧
        (Ideal.absNorm (good i) : ℝ) ≤ B / Q := by
      refine ⟨goodSquarefreePart_admissible _, ?_, ?_⟩
      · rw [show B / Q / 2 = (B / 2) / Q by ring]
        apply (div_le_iff₀ hQp).2
        have hx := (hrows i).2.1
        rw [hn i] at hx
        nlinarith
      · exact (le_div_iff₀ hQp).2 (by simpa only [mul_comm] using (hn i).symm.trans_le (hrows i).2.2)
    have hBQ : 1 ≤ B / Q := by
      have hh : 1 ≤ (Ideal.absNorm (good i₀) : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun h => (hg i₀).1.1 (Ideal.absNorm_eq_zero_iff.mp h)))
      exact hh.trans (hg i₀).2.2
    have hZa (i : m) : Z i ≤ U * (N * Real.sqrt (F / ((M * Q) * (Ideal.absNorm (good i) : ℝ)))) := by
      simpa only [hn i, mul_assoc] using hZ i
    have hbnd := hexp.dual_truncated_middle deltaLoss hδ ε hε (B / Q) N (M * Q) F U hBQ hN
      (by positivity) hF hU good left right hgr hl hri hg a' b' W Y Z lengthScale hleft hright hZa
    change ‖dualTruncatedMiddle W good left right a' b' (M * Q) F Y Z lengthScale‖ ≤
      dualMiddleMajorant hexp deltaLoss hδ ε hε (B / Q) N (M * Q) F U a' b' W at hbnd
    have htr := unrestrictedDualTruncatedMiddle_sector W rows left right a b M F Y Z lengthScale
      (fun i => (hrows i).1) (fun j => (hleft j).1) (fun k => (hright k).1) hray E hE hQnz
    change unrestrictedDualTruncatedMiddle W rows left right a b M F Y Z lengthScale =
      ((1 / Q : ℝ) : ℂ) * dualTruncatedMiddle W good left right a' b' (M * Q) F Y Z lengthScale at htr
    rw [htr, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / Q)]
    apply (mul_le_mul_of_nonneg_left hbnd (by positivity)).trans
    have hae (j : n) : ‖a' j‖ ≤ ‖a j‖ := by
      dsimp only [a']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)
    have hbe (k : p) : ‖b' k‖ ≤ ‖b k‖ := by
      dsimp only [b']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)
    have he := divisorEnergyFactor_mono_coefficients ε hε N a a' b b' hae hbe
    have hp : ((B / Q) * N) ^ deltaLoss ≤ (B * N) ^ deltaLoss := by
      apply Real.rpow_le_rpow (by positivity) _ hδ.le
      exact mul_le_mul_of_nonneg_right (div_le_self (by linarith) hQ) (by linarith)
    have hs := dual_bad_sector_scale M F B Q U α hM hF (by linarith) hQ hU hα
    have hc := nonzeroLatticeEnvelopeConstant_nonneg
    have hW := dualMiddleDecayConstant_nonneg W
    have hea := divisorEnergyFactor_nonneg ε hε N a' b'
    have heb := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    unfold dualMiddleMajorant
    calc
      _ = ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a' b' * (divisorExponentConstant hexp deltaLoss hδ * ((B / Q) * N) ^ deltaLoss) *
            ((1 / Q) * (M * Q / F + (2 * U) * Real.sqrt (M * Q / F) * (B / Q) ^ (α - 1 / 2)))) := by ring
      _ ≤ _ := by gcongr

end


end CanonicalQuadraticSieve


end

end OAI

end


