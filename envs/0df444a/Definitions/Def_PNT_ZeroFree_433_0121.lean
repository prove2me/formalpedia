-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0121
-- name    : PNT_ZeroFree_433_0121
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:48:39.442391+00:00
-- url     : https://prove2.me/theorems/fb88447a-a3bd-4d5f-a0c4-d97db6c5c75e
-- title:
--   Zero-free region foundations: QuadraticSieve.PrincipalMajorants [0121]
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
import Definitions.Def_PNT_ZeroFree_433_0051
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0072
import Definitions.Def_PNT_ZeroFree_433_0082
import Definitions.Def_PNT_ZeroFree_433_0092
import Definitions.Def_PNT_ZeroFree_433_0098
import Definitions.Def_PNT_ZeroFree_433_0103
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0114
import Definitions.Def_PNT_ZeroFree_433_0118_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0119
import Definitions.Def_PNT_ZeroFree_433_0119_parallel1
import Definitions.Def_PNT_ZeroFree_433_0120_parallel1
import Definitions.Def_PNT_ZeroFree_433_0121_parallel1
import Definitions.Def_PNT_ZeroFree_433_0131_parallel2
import Definitions.Def_PNT_ZeroFree_433_0136_parallel2
import Definitions.Def_PNT_ZeroFree_433_0144_parallel2
import Definitions.Def_PNT_ZeroFree_433_0158_parallel2

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


variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]


omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma unrestrictedSmallPrincipalSum_sector
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop)
    (hrows : ∀ i, Squarefree (rows i)) (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E) :
    unrestrictedSmallPrincipalSum rows left right a b M F P =
      signedProductDivisorSum (fun i => goodSquarefreePart (rows i)) left right
        (fun j => a j*quadraticRow (left j) (idealGenerator (sectorBadIdeal E)))
        (fun k => b k*quadraticRow (right k) (idealGenerator (sectorBadIdeal E))) P
        (fun _ _ j k => ((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ)) := by
  unfold unrestrictedSmallPrincipalSum signedProductDivisorSum
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [unrestrictedPairTerm_sector rows left right a b hrows hleft hright hray E hE i j k]

theorem HasSieveExponent.small_principal_sector {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Squarefree (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ N/2 ≤ (Ideal.absNorm (left j):ℝ) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N/2 ≤ (Ideal.absNorm (right k):ℝ) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ d i, P d i → (Ideal.absNorm d:ℝ) ≤ U*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ)))))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E) :
    ‖unrestrictedSmallPrincipalSum rows left right a b M F P‖ ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b := by
  classical
  cases isEmpty_or_nonempty m with
  | inl hempty =>
    let := hempty
    simp only [unrestrictedSmallPrincipalSum, Finset.univ_eq_empty, Finset.sum_empty, norm_zero]
    exact smallPrincipalMajorant_nonneg hexp deltaLoss hδ ε hε B N M F U a b (by linarith) (by linarith) hM.le hF.le hU
  | inr hnonempty =>
    let := hnonempty
    let i₀ : m := Classical.choice hnonempty
    let Q : ℝ := Ideal.absNorm (sectorBadIdeal E)
    let good := fun i => goodSquarefreePart (rows i)
    let a' := fun j => a j*quadraticRow (left j) (idealGenerator (sectorBadIdeal E))
    let b' := fun k => b k*quadraticRow (right k) (idealGenerator (sectorBadIdeal E))
    have hQnz := sectorBadIdeal_ne_zero_of_row (rows i₀) (hrows i₀).1 E (hE i₀)
    have hQ : 1 ≤ Q := by
      dsimp only [Q]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun h => hQnz (Ideal.absNorm_eq_zero_iff.mp h)))
    have hQp : 0 < Q := by linarith
    have hn (i : m) : (Ideal.absNorm (rows i):ℝ) = Q*(Ideal.absNorm (good i):ℝ) := by
      have hi := congrArg (fun I : Ideal O => (Ideal.absNorm I:ℝ))
        (sector_bad_good_product (rows i) (hrows i).1 E (hE i))
      simpa only [map_mul,Nat.cast_mul] using hi.symm
    have hgr : Function.Injective good := by
      intro i k h
      exact hr (goodSquarefreePart_injective_on_sector _ _ (hrows i).1 (hrows k).1
        ((hE i).trans (hE k).symm) h)
    have hg (i : m) : Admissible (good i) ∧ (B/Q)/2 ≤ (Ideal.absNorm (good i):ℝ) ∧
        (Ideal.absNorm (good i):ℝ) ≤ B/Q := by
      refine ⟨goodSquarefreePart_admissible _, ?_, ?_⟩
      · rw [show B/Q/2 = (B/2)/Q by ring]
        apply (div_le_iff₀ hQp).2
        have hx := (hrows i).2.1
        rw [hn i] at hx
        nlinarith
      · exact (le_div_iff₀ hQp).2 (by simpa only [mul_comm] using (hn i).symm.trans_le (hrows i).2.2)
    have hBQ : 1 ≤ B/Q := by
      have hh : 1 ≤ (Ideal.absNorm (good i₀):ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun h => (hg i₀).1.1 (Ideal.absNorm_eq_zero_iff.mp h)))
      exact hh.trans (hg i₀).2.2
    have hPg (d : Ideal O) (i : m) (hp : P d i) : (Ideal.absNorm d:ℝ) ≤
        U*(N*Real.sqrt (F/(M*(Ideal.absNorm (good i):ℝ)))) := by
      apply (hP d i hp).trans
      have hgoodpos : 0 < (Ideal.absNorm (good i):ℝ) := by
        exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => (hg i).1.1 (Ideal.absNorm_eq_zero_iff.mp h))
      have hng : (Ideal.absNorm (good i):ℝ) ≤ (Ideal.absNorm (rows i):ℝ) :=
        Nat.cast_le.mpr (goodSquarefreePart_norm_le (rows i) (hrows i).1)
      gcongr
    rw [unrestrictedSmallPrincipalSum_sector rows left right a b M F P
      (fun i => (hrows i).1) (fun j => (hleft j).1) (fun k => (hright k).1) hray E hE]
    have hbnd := hexp.small_principal_divisor_sum deltaLoss hδ ε hε (B/Q) N M F U hBQ hN hM hF hU
      good left right hgr hl hri hg hleft hright a' b' P hPg
    change ‖signedProductDivisorSum good left right a' b' P _‖ ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b
    apply hbnd.trans
    apply smallPrincipalMajorant_mono hexp hα deltaLoss hδ ε hε (B/Q) B N M F U a a' b b'
      (by positivity) (div_le_self (by linarith) hQ) (by linarith) hM.le hF.le hU
    · intro j
      dsimp only [a']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)
    · intro k
      dsimp only [b']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)

theorem HasSieveExponent.unrestricted_small_principal_sum {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Squarefree (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ N/2 ≤ (Ideal.absNorm (left j):ℝ) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N/2 ≤ (Ideal.absNorm (right k):ℝ) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ d i, P d i → (Ideal.absNorm d:ℝ) ≤ U*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))) :
    ‖unrestrictedSmallPrincipalSum rows left right a b M F P‖ ≤
      4*smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b := by
  classical
  let σ := fun i => badPrimeSector (rows i)
  have hs : unrestrictedSmallPrincipalSum rows left right a b M F P =
      ∑ E : fixedBadPrimes.powerset, unrestrictedSmallPrincipalSum
        (fun i : {i // σ i = E} => rows i.val) left right a b M F (fun d i => P d i.val) := by
    unfold unrestrictedSmallPrincipalSum
    exact (Fintype.sum_fiberwise σ _).symm
  have hb (E : fixedBadPrimes.powerset) :
      ‖unrestrictedSmallPrincipalSum (fun i : {i // σ i = E} => rows i.val)
        left right a b M F (fun d i => P d i.val)‖ ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b :=
    hexp.small_principal_sector hα deltaLoss hδ ε hε B N M F U hB hN hM hF hU
      (fun i : {i // σ i = E} => rows i.val) left right (fun i k h => Subtype.ext (hr h)) hl hri
      (fun i => hrows i.val) hleft hright hray a b (fun d i => P d i.val) (fun d i => hP d i.val)
      E (fun i => i.property)
  rw [hs]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _E : fixedBadPrimes.powerset, smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b :=
      Finset.sum_le_sum (fun E _ => hb E)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe, fixedBadPrimes_powerset_card]
      norm_num

end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum


variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]


theorem HasSieveExponent.masked_source_large_principal_sum {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε) (G : Ideal O) (hG : G ≠ 0)
    (B N M T : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hT : 0 < T)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (hGl : ∀ j, IsCoprime G (left j)) (hGr : ∀ k, IsCoprime G (right k))
    (a : n → ℂ) (b : p → ℂ) (Z : m → ℝ)
    (hZ : ∀ i, T*Real.sqrt (M/(Ideal.absNorm (rows i):ℝ)) ≤ Z i) :
    ‖maskedPrincipalDivisorCorrection G rows left right a b M Z‖ ≤
      (idealDivisors G).card * (((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (4*N/T+Real.sqrt M*B^(α-1/2)))) := by
  classical
  let V := ((columnDyadicLength N+1:ℕ):ℝ)^2 *
    (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
      (4*N/T+Real.sqrt M*B^(α-1/2)))
  have hqbound (q : Ideal O) (hq : q ∈ idealDivisors G) :
      ‖principalDivisorCorrection rows left right a b (M/(Ideal.absNorm q:ℝ)^2)
        (fun d i => Z i/(Ideal.absNorm q:ℝ) < (Ideal.absNorm d:ℝ))‖ ≤ V := by
    have hqG := (mem_idealDivisors hG).mp hq
    have hq0 : q ≠ 0 := by intro he; rw [he,zero_dvd_iff] at hqG; exact hG hqG
    have hq1 : 1 ≤ (Ideal.absNorm q:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun he => hq0 (Ideal.absNorm_eq_zero_iff.mp he))
    have hqpos : 0 < (Ideal.absNorm q:ℝ) := by linarith
    have hZq (i : m) : T*Real.sqrt ((M/(Ideal.absNorm q:ℝ)^2)/(Ideal.absNorm (rows i):ℝ)) ≤
        Z i/(Ideal.absNorm q:ℝ) := by
      rw [←sqrt_norm_divisor_scale M _ _ hM.le (Nat.cast_nonneg _) hqpos]
      calc
        _ = (T*Real.sqrt (M/(Ideal.absNorm (rows i):ℝ)))/(Ideal.absNorm q:ℝ) := by ring
        _ ≤ _ := div_le_div_of_nonneg_right (hZ i) hqpos.le
    apply (hexp.source_large_principal_sum deltaLoss hδ ε hε B N (M/(Ideal.absNorm q:ℝ)^2) T
      hB hN (by positivity) hT rows left right hr hl hri hrows hleft hright a b
        (fun i => Z i/(Ideal.absNorm q:ℝ)) hZq).trans
    have he := divisorEnergyFactor_nonneg ε hε N a b
    have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    dsimp only [V]
    gcongr
    exact div_le_self hM.le (one_le_pow₀ hq1)
  rw [maskedPrincipalDivisorCorrection_eq G hG rows left right a b M hM.le Z
    (fun j => (hleft j).1.1) (fun k => (hright k).1.1) hGl hGr]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ q ∈ idealDivisors G, V := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (QuadraticInitialBound.norm_ideal_moebius_le_one q)).trans (hqbound q hq)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,V]

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open IdealMobiusDivisorSum


variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]


theorem HasSieveExponent.large_principal_sector {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F T : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hT : 4 ≤ T)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Squarefree (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (a : n → ℂ) (b : p → ℂ) (Z : m → ℝ)
    (hZ : ∀ i, T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ)))) ≤ Z i)
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E) :
    ‖unrestrictedLargePrincipalSum rows left right a b M F Z‖ ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a b := by
  classical
  cases isEmpty_or_nonempty m with
  | inl hempty =>
    let := hempty
    simp only [unrestrictedLargePrincipalSum,Finset.univ_eq_empty,Finset.sum_empty,norm_zero]
    exact smallPrincipalMajorant_nonneg hexp deltaLoss hδ ε hε B N M F (1/2) a b
      (by linarith) (by linarith) hM.le hF.le (by norm_num)
  | inr hnonempty =>
    let := hnonempty
    let i₀ : m := Classical.choice hnonempty
    let Q : ℝ := Ideal.absNorm (sectorBadIdeal E)
    let good := fun i => goodSquarefreePart (rows i)
    let a' := fun j => a j*quadraticRow (left j) (idealGenerator (sectorBadIdeal E))
    let b' := fun k => b k*quadraticRow (right k) (idealGenerator (sectorBadIdeal E))
    have hQnz := sectorBadIdeal_ne_zero_of_row (rows i₀) (hrows i₀).1 E (hE i₀)
    have hQ : 1 ≤ Q := by
      dsimp only [Q]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun h => hQnz (Ideal.absNorm_eq_zero_iff.mp h)))
    have hQp : 0 < Q := by linarith
    have hn (i : m) : (Ideal.absNorm (rows i):ℝ) = Q*(Ideal.absNorm (good i):ℝ) := by
      have hi := congrArg (fun I : Ideal O => (Ideal.absNorm I:ℝ))
        (sector_bad_good_product (rows i) (hrows i).1 E (hE i))
      simpa only [map_mul,Nat.cast_mul] using hi.symm
    have hgr : Function.Injective good := by
      intro i k h
      exact hr (goodSquarefreePart_injective_on_sector _ _ (hrows i).1 (hrows k).1
        ((hE i).trans (hE k).symm) h)
    have hg (i : m) : Admissible (good i) ∧ (B/Q)/2 ≤ (Ideal.absNorm (good i):ℝ) ∧
        (Ideal.absNorm (good i):ℝ) ≤ B/Q := by
      refine ⟨goodSquarefreePart_admissible _, ?_, ?_⟩
      · rw [show B/Q/2 = (B/2)/Q by ring]
        apply (div_le_iff₀ hQp).2
        have hx := (hrows i).2.1
        rw [hn i] at hx
        nlinarith
      · exact (le_div_iff₀ hQp).2 (by simpa only [mul_comm] using (hn i).symm.trans_le (hrows i).2.2)
    have hBQ : 1 ≤ B/Q := by
      have hh : 1 ≤ (Ideal.absNorm (good i₀):ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun h => (hg i₀).1.1 (Ideal.absNorm_eq_zero_iff.mp h)))
      exact hh.trans (hg i₀).2.2
    have hZg (i : m) : T*(N*Real.sqrt (F/((M*Q)*(Ideal.absNorm (good i):ℝ)))) ≤ Z i := by
      simpa only [hn i,mul_assoc] using hZ i
    have hbnd := hexp.dual_large_principal_sum deltaLoss hδ ε hε (B/Q) N (M*Q) F T hBQ hN
      (by positivity) hF (by linarith) good left right hgr hl hri hg hleft hright a' b' Z hZg
    have hmajor : ‖principalDivisorCorrection good left right a' b' ((M*Q)/F)
        (fun d i => Z i < (Ideal.absNorm d:ℝ))‖ ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε (B/Q) N (M*Q) F (1/2) a' b' := by
      apply hbnd.trans
      have ht : 4/T ≤ 1 := (div_le_one (by linarith : 0<T)).mpr hT
      have hlead : 4*(M*Q)/(F*T) ≤ (M*Q)/F := by
        calc
          _ = ((M*Q)/F)*(4/T) := by ring
          _ ≤ _ := mul_le_of_le_one_right (by positivity) ht
      have he := divisorEnergyFactor_nonneg ε hε N a' b'
      have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
      unfold smallPrincipalMajorant
      norm_num only [show (2:ℝ)*(1/2)=1 by norm_num,one_mul]
      gcongr
    have htr := unrestrictedLargePrincipalSum_sector rows left right a b M F Z hM hF
      (fun i => (hrows i).1) (fun j => (hleft j).1) (fun k => (hright k).1) hray E hE hQnz
    change unrestrictedLargePrincipalSum rows left right a b M F Z =
      ((1/Q:ℝ):ℂ)*principalDivisorCorrection good left right a' b' ((M*Q)/F)
        (fun d i => Z i < (Ideal.absNorm d:ℝ)) at htr
    rw [htr,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤1/Q)]
    apply (mul_le_mul_of_nonneg_left hmajor (by positivity)).trans
    apply smallPrincipalMajorant_bad_scale hexp hα deltaLoss hδ ε hε B N M F (1/2) Q a a' b b'
      (by linarith) (by linarith) hM hF (by norm_num) hQ
    · intro j
      dsimp only [a']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)
    · intro k
      dsimp only [b']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)

theorem HasSieveExponent.unrestricted_large_principal_sum {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F T : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hT : 4 ≤ T)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Squarefree (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (a : n → ℂ) (b : p → ℂ) (Z : m → ℝ)
    (hZ : ∀ i, T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ)))) ≤ Z i) :
    ‖unrestrictedLargePrincipalSum rows left right a b M F Z‖ ≤
      4*smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a b := by
  classical
  let σ := fun i => badPrimeSector (rows i)
  have hs : unrestrictedLargePrincipalSum rows left right a b M F Z =
      ∑ E : fixedBadPrimes.powerset, unrestrictedLargePrincipalSum
        (fun i : {i // σ i = E} => rows i.val) left right a b M F (fun i => Z i.val) := by
    unfold unrestrictedLargePrincipalSum
    exact (Fintype.sum_fiberwise σ _).symm
  have hb (E : fixedBadPrimes.powerset) :
      ‖unrestrictedLargePrincipalSum (fun i : {i // σ i = E} => rows i.val)
        left right a b M F (fun i => Z i.val)‖ ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a b :=
    hexp.large_principal_sector hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT
      (fun i : {i // σ i = E} => rows i.val) left right (fun i k h => Subtype.ext (hr h)) hl hri
      (fun i => hrows i.val) hleft hright hray a b (fun i => Z i.val) (fun i => hZ i.val)
      E (fun i => i.property)
  rw [hs]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _E : fixedBadPrimes.powerset, smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a b :=
      Finset.sum_le_sum (fun E _ => hb E)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_coe,fixedBadPrimes_powerset_card]
      norm_num

end


end CanonicalQuadraticSieve

end

end OAI

end


