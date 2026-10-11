-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0052
-- name    : PNT_ZeroFree_433_0052
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T15:19:44.42498+00:00
-- url     : https://prove2.me/theorems/d4530f1e-98cc-4298-8210-3265b259bee8
-- title:
--   Zero-free region foundations: QuadraticSieve.InitialBound [0052]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.InitialBound
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/InitialBound.lean#L77-L627

import Definitions.Def_PNT_ZeroFree_433_0034
import Definitions.Def_PNT_ZeroFree_433_0051

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/InitialBound.lean#L77-L627
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.QuadraticSieve.InitialBound
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

open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def quadraticRow {α : Type*} (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset α) (z : O) : ℂ :=
  (finiteSquarefreeRow P hg S z) ^ 3

theorem quadraticRow_eq_canonical {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset α) (z : O) :
    quadraticRow P hg S z =
      finiteSexticRow (fun i : S => P i.val) (fun i => hg i.val) (fun _ => 3) z := by
  simp only [quadraticRow, finiteSexticRow, finiteSquarefreeRow,
    MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), Finset.prod_pow]
  rw [Finset.prod_coe_sort (s := S) (f := fun i => canonicalSextic (P i) (hg i) (Ideal.Quotient.mk (P i) z))]

theorem quadraticRow_star {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset α) (z : O) :
    star (quadraticRow P hg S z) = quadraticRow P hg S z := by
  rw [quadraticRow_eq_canonical]
  simp only [finiteSexticRow, star_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [canonicalSextic_pow_three_quadratic]
  simp only [MulChar.ringHomComp_apply, Int.coe_castRingHom, star_intCast]

theorem quadraticRow_disjoint_union {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S T : Finset α) (hd : Disjoint S T) (z : O) :
    quadraticRow P hg (S ∪ T) z = quadraticRow P hg S z * quadraticRow P hg T z := by
  simp only [quadraticRow, finiteSquarefreeRow, Finset.prod_union hd, mul_pow]

theorem quadraticRow_pair_kernel {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S T : Finset α) (z : O) :
    star (quadraticRow P hg S z) * quadraticRow P hg T z =
      rowCoprimeMask P (S ∩ T) z *
        finiteSexticRow (activePrimes P S T) (fun i => hg i.val) (fun _ => 3) z := by
  have h := congrArg (fun v : ℂ => v ^ 3) (finiteSquarefreeRow_pair_kernel P hg S T z)
  have hm : rowCoprimeMask P (S ∩ T) z ^ 3 = rowCoprimeMask P (S ∩ T) z := by
    unfold rowCoprimeMask
    split_ifs <;> simp
  have hd : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  simp only [mul_pow, ← star_pow, hm] at h
  change star (quadraticRow P hg S z) * quadraticRow P hg T z =
    rowCoprimeMask P (S ∩ T) z * star (quadraticRow P hg (S \ T) z) *
      quadraticRow P hg (T \ S) z at h
  simp only [quadraticRow_star] at h ⊢
  rw [← quadraticRow_eq_canonical]
  change _ = rowCoprimeMask P (S ∩ T) z * quadraticRow P hg ((S \ T) ∪ (T \ S)) z
  rw [quadraticRow_disjoint_union P hg _ _ hd]
  simpa only [mul_assoc] using h

theorem quadratic_gram_offdiagonal {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, lambda ∉ P i) (hc : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (S T : Finset α) (hne : S ≠ T) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, (star (quadraticRow P hg S z) * quadraticRow P hg T z) *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      (2 : ℝ) ^ (S ∩ T).card *
        (pvControl W * ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖) := by
  let : Nonempty (activeSupport S T) := (activeSupport_nonempty_of_ne hne).to_subtype
  simp_rw [quadraticRow_pair_kernel P hg S T]
  exact canonical_masked_polya_vinogradov P hinj (S ∩ T) (activePrimes P S T)
    (activePrimes_pairwise_isCoprime P hinj S T) (fun i => hg i.val)
    (fun i => hc i.val) (fun _ => 3) (fun _ => by decide) (fun _ => by decide) W M hM

def supportNorm {α : Type*} (P : α → Ideal O) (S : Finset α) : ℝ :=
  Ideal.absNorm (∏ i ∈ S, P i)

theorem supportNorm_nonneg {α : Type*} (P : α → Ideal O) (S : Finset α) :
    0 ≤ supportNorm P S := Nat.cast_nonneg _

theorem two_pow_card_le_supportNorm {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (S : Finset α) :
    (2 : ℝ) ^ S.card ≤ supportNorm P S := by
  have hnorm (i : α) : (2 : ℝ) ≤ Ideal.absNorm (P i) := by
    have h0 : Ideal.absNorm (P i) ≠ 0 := by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]
      exact NeZero.ne (P i)
    have h1 : Ideal.absNorm (P i) ≠ 1 := by
      rw [ne_eq, Ideal.absNorm_eq_one_iff]
      exact (inferInstance : (P i).IsMaximal).ne_top
    exact_mod_cast (show 2 ≤ Ideal.absNorm (P i) by omega)
  change (2 : ℝ) ^ S.card ≤ (Ideal.absNorm (∏ i ∈ S, P i) : ℝ)
  rw [map_prod, Nat.cast_prod]
  calc
    _ = ∏ _i ∈ S, (2 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => by norm_num) (fun i _ => hnorm i)

theorem divisor_conductor_bound {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (S T : Finset α)
    (N : ℝ) (hN : 0 ≤ N) (hS : supportNorm P S ≤ N) (hT : supportNorm P T ≤ N) :
    (2 : ℝ) ^ (S ∩ T).card *
      ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖ ≤ N := by
  have hid := congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ))
    (activeSupport_product_mul_common_sq P S T)
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow] at hid
  rw [← activePrimeModulus_norm_sq] at hid
  change ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖ ^ 2 *
    (supportNorm P (S ∩ T)) ^ 2 = supportNorm P S * supportNorm P T at hid
  have hpow := two_pow_card_le_supportNorm P (S ∩ T)
  have hmul := mul_le_mul_of_nonneg_right hpow
    (norm_nonneg (eisEmbedding (finitePrimeModulus (activePrimes P S T))))
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (2 : ℝ) ^ (S ∩ T).card *
    ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖) hmul 2
  have hprod := mul_le_mul hS hT (supportNorm_nonneg P T) hN
  nlinarith

theorem quadratic_gram_offdiagonal_of_norm_le {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, lambda ∉ P i) (hc : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (S T : Finset α) (hne : S ≠ T) (N : ℝ) (hN : 0 ≤ N)
    (hS : supportNorm P S ≤ N) (hT : supportNorm P T ≤ N)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, (star (quadraticRow P hg S z) * quadraticRow P hg T z) *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤ pvControl W * N := by
  apply (quadratic_gram_offdiagonal P hinj hg hc S T hne W M hM).trans
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (divisor_conductor_bound P S T N hN hS hT)
    (pvControl_nonneg W)

def diagonalControl (W : 𝓢(ℝ, ℂ)) : ℝ :=
  16 * (1 + Real.pi) ^ 2 *
    (Finset.Iic (2, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W

theorem diagonalControl_nonneg (W : 𝓢(ℝ, ℂ)) : 0 ≤ diagonalControl W := by
  unfold diagonalControl
  positivity

theorem radial_weight_lattice_bound (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    (∑' z : O, ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) ≤ diagonalControl W * M := by
  have hMp : 0 < M := by linarith
  let t := M⁻¹
  have ht : 0 < t := inv_pos.mpr hMp
  have ht1 : t ≤ 1 := (inv_le_one₀ hMp).mpr hM
  let B := 4 * (Finset.Iic (2, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hp (z : O) : ‖W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      B * ((1 + t * ‖eisEmbedding z‖ ^ 2) ^ 2)⁻¹ := by
    have hq : 0 ≤ ‖eisEmbedding z‖ ^ 2 / M := div_nonneg (sq_nonneg _) hMp.le
    have hh := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (2, 0)) (k := 2) (n := 0) le_rfl le_rfl W (‖eisEmbedding z‖ ^ 2 / M)
    simp only [norm_iteratedFDeriv_zero, Real.norm_of_nonneg hq] at hh
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hh
    change (1 + ‖eisEmbedding z‖ ^ 2 / M) ^ 2 * ‖W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤ B at hh
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [t, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh
  have hs : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hMp)
  have hb := hs.tsum_le_tsum hp ((scaled_eisenstein_cauchy_summable t ht).mul_left B)
  rw [tsum_mul_left] at hb
  have hsmall := scaled_eisenstein_cauchy_small t ht ht1
  have hmul := mul_le_mul_of_nonneg_left hb ht.le
  have hcontrol := mul_le_mul_of_nonneg_left hsmall hB
  have hfinal : t * (∑' z : O, ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) ≤ diagonalControl W := by
    unfold diagonalControl
    dsimp [B] at hcontrol hmul
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hfinal hMp.le
  simpa only [t, ← mul_assoc, mul_inv_cancel₀ hMp.ne', one_mul, mul_comm] using hh

theorem quadraticRow_norm_le_one {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset α) (z : O) :
    ‖quadraticRow P hg S z‖ ≤ 1 := by
  rw [quadraticRow_eq_canonical]
  exact finiteSexticRow_norm_le_one _ _ _ _

theorem quadratic_pair_summable {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S T : Finset α)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => (star (quadraticRow P hg S z) * quadraticRow P hg T z) *
      W (‖eisEmbedding z‖ ^ 2 / M)) := by
  have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hM)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hW
  intro z
  rw [norm_mul, norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_mul (quadraticRow_norm_le_one P hg S z) (quadraticRow_norm_le_one P hg T z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

theorem quadratic_gram_diagonal {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset α)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    ‖∑' z : O, (star (quadraticRow P hg S z) * quadraticRow P hg S z) *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤ diagonalControl W * M := by
  have hMp : 0 < M := by linarith
  have hs := (quadratic_pair_summable P hg S S W M hMp).norm
  have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hMp)
  refine (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum ?_ hW).trans
    (radial_weight_lattice_bound W M hM))
  intro z
  rw [norm_mul, norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_mul (quadraticRow_norm_le_one P hg S z) (quadraticRow_norm_le_one P hg S z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

private theorem norm_sq_finite_sum {β : Type*} (C : Finset β) (a r : β → ℂ) :
    (↑(‖∑ n ∈ C, a n * r n‖ ^ 2) : ℂ) =
      ∑ n ∈ C, ∑ m ∈ C, (star (a n) * a m) * (star (r n) * r m) := by
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, map_mul, starRingEnd_apply]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem quadratic_mean_summable {α β : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (C : Finset β) (support : β → Finset α) (a : β → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * quadraticRow P hg (support n) z‖ ^ 2) : ℂ)) := by
  have hs := summable_sum (s := C) (fun n hn => summable_sum (s := C) (fun m hm =>
    (quadratic_pair_summable P hg (support n) (support m) W M hM).mul_left (star (a n) * a m)))
  apply hs.congr
  intro z
  rw [norm_sq_finite_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem quadratic_mean_expand {α β : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (C : Finset β) (support : β → Finset α) (a : β → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * quadraticRow P hg (support n) z‖ ^ 2) : ℂ)) =
      ∑ n ∈ C, ∑ m ∈ C, (star (a n) * a m) *
        ∑' z : O, (star (quadraticRow P hg (support n) z) * quadraticRow P hg (support m) z) *
          W (‖eisEmbedding z‖ ^ 2 / M) := by
  let f : β → β → O → ℂ := fun n m z => (star (a n) * a m) *
    ((star (quadraticRow P hg (support n) z) * quadraticRow P hg (support m) z) *
      W (‖eisEmbedding z‖ ^ 2 / M))
  have hf (n m : β) : Summable (f n m) :=
    (quadratic_pair_summable P hg (support n) (support m) W M hM).mul_left _
  have heq (z : O) : W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * quadraticRow P hg (support n) z‖ ^ 2) : ℂ) =
        ∑ n ∈ C, ∑ m ∈ C, f n m z := by
    rw [norm_sq_finite_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    dsimp [f]
    ring
  rw [tsum_congr heq, Summable.tsum_finsetSum (fun n hn => summable_sum (fun m hm => hf n m))]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Summable.tsum_finsetSum (fun m hm => hf n m)]
  apply Finset.sum_congr rfl
  intro m hm
  exact tsum_mul_left

theorem quadratic_initial_mean_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, lambda ∉ P i) (hc : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (C : Finset β) (support : β → Finset α)
    (hsupp : Set.InjOn support (↑C : Set β))
    (N : ℝ) (hN : 0 ≤ N) (hNorm : ∀ n ∈ C, supportNorm P (support n) ≤ N)
    (a : β → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    ‖∑' z : O, W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * quadraticRow P hg (support n) z‖ ^ 2) : ℂ)‖ ≤
        (diagonalControl W * M + pvControl W * N * C.card) * ∑ n ∈ C, ‖a n‖ ^ 2 := by
  have hMp : 0 < M := by linarith
  let D := diagonalControl W * M
  let B := pvControl W * N
  have hB : 0 ≤ B := mul_nonneg (pvControl_nonneg W) hN
  let K : β → β → ℂ := fun n m => ∑' z : O,
    (star (quadraticRow P hg (support n) z) * quadraticRow P hg (support m) z) *
      W (‖eisEmbedding z‖ ^ 2 / M)
  have hK (n : β) (hn : n ∈ C) (m : β) (hm : m ∈ C) :
      ‖K n m‖ ≤ (if n = m then D else 0) + B := by
    by_cases hnm : n = m
    · subst m
      simp only [ite_true]
      exact (quadratic_gram_diagonal P hg (support n) W M hM).trans (le_add_of_nonneg_right hB)
    · simp only [hnm, ite_false, zero_add]
      exact quadratic_gram_offdiagonal_of_norm_le P hinj hg hc _ _
        (fun h => hnm (hsupp hn hm h)) N hN (hNorm n hn) (hNorm m hm) W M hMp
  have heq (n : β) (hn : n ∈ C) :
      (∑ m ∈ C, ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B)) =
        D * ‖a n‖ ^ 2 + B * ‖a n‖ * ∑ m ∈ C, ‖a m‖ := by
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq,  hn, ite_true]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hcalc : (∑ n ∈ C, ∑ m ∈ C,
      ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B)) =
      D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * (∑ n ∈ C, ‖a n‖) ^ 2 := by
    rw [Finset.sum_congr rfl heq]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [quadratic_mean_expand P hg C support a W M hMp]
  calc
    _ ≤ ∑ n ∈ C, ∑ m ∈ C, ‖(star (a n) * a m) * K n m‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ n ∈ C, ∑ m ∈ C, ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B) := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      simp only [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (hK n hn m hm) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * (∑ n ∈ C, ‖a n‖) ^ 2 := hcalc
    _ ≤ D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * ((C.card : ℝ) * ∑ n ∈ C, ‖a n‖ ^ 2) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ hB
      simpa only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, mul_comm] using
        Finset.sum_mul_sq_le_sq_mul_sq C (fun n => ‖a n‖) (fun _ => (1 : ℝ))
    _ = _ := by dsimp [D, B]; ring

def sieveBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def sieveCutoff : 𝓢(ℝ, ℂ) := by
  have hc : HasCompactSupport (fun t : ℝ => (sieveBump t : ℂ)) :=
    sieveBump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hs : ContDiff ℝ ∞ (fun t : ℝ => (sieveBump t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp sieveBump.contDiff
  exact hc.toSchwartzMap hs

@[simp] theorem sieveCutoff_apply (t : ℝ) : sieveCutoff t = (sieveBump t : ℂ) := rfl

theorem sieveBump_eq_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : sieveBump t = 1 := by
  apply sieveBump.one_of_mem_closedBall
  change dist t 0 ≤ 1
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht0] using ht1

theorem quadratic_initial_finite_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, lambda ∉ P i) (hc : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (C : Finset β) (support : β → Finset α) (hsupp : Set.InjOn support (↑C : Set β))
    (N : ℝ) (hN : 0 ≤ N) (hNorm : ∀ n ∈ C, supportNorm P (support n) ≤ N)
    (a : β → ℂ) (M : ℝ) (hM : 1 ≤ M) (R : Finset O)
    (hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M) :
    (∑ z ∈ R, ‖∑ n ∈ C, a n * quadraticRow P hg (support n) z‖ ^ 2) ≤
      (diagonalControl sieveCutoff * M + pvControl sieveCutoff * N * C.card) *
        ∑ n ∈ C, ‖a n‖ ^ 2 := by
  have hMp : 0 < M := by linarith
  let E : O → ℝ := fun z => ‖∑ n ∈ C, a n * quadraticRow P hg (support n) z‖ ^ 2
  let F : O → ℝ := fun z => sieveBump (‖eisEmbedding z‖ ^ 2 / M) * E z
  let H : O → ℂ := fun z => sieveCutoff (‖eisEmbedding z‖ ^ 2 / M) * (E z : ℂ)
  have hF (z : O) : 0 ≤ F z := mul_nonneg sieveBump.nonneg (sq_nonneg _)
  have hH (z : O) : H z = (F z : ℂ) := by
    simp only [H, F, sieveCutoff_apply, Complex.ofReal_mul]
  have hHs : Summable H := quadratic_mean_summable P hg C support a sieveCutoff M hMp
  have hFs : Summable F := hHs.norm.congr (fun z => by
    rw [hH, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hF z)])
  have hsum : ‖∑' z : O, H z‖ = ∑' z : O, F z := by
    rw [tsum_congr hH, ← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (tsum_nonneg hF)]
  calc
    _ = ∑ z ∈ R, F z := by
      apply Finset.sum_congr rfl
      intro z hz
      have ht0 : 0 ≤ ‖eisEmbedding z‖ ^ 2 / M := div_nonneg (sq_nonneg _) hMp.le
      have ht1 : ‖eisEmbedding z‖ ^ 2 / M ≤ 1 := (div_le_one hMp).mpr (hR z hz)
      simp only [F, sieveBump_eq_one ht0 ht1, one_mul, E]
    _ ≤ ∑' z : O, F z := hFs.sum_le_tsum R (fun z _ => hF z)
    _ = ‖∑' z : O, H z‖ := hsum.symm
    _ ≤ _ := quadratic_initial_mean_bound P hinj hg hc C support hsupp N hN hNorm
      a sieveCutoff M hM

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open ConcretePrimeRowBridge ShortDraftHeckeBridge

def initialSieveConstant : ℝ :=
  diagonalControl sieveCutoff + 128 * pvControl sieveCutoff + 1

theorem initialSieveConstant_pos : 0 < initialSieveConstant := by
  have := diagonalControl_nonneg sieveCutoff
  have := pvControl_nonneg sieveCutoff
  unfold initialSieveConstant
  positivity

theorem ideal_initial_quadratic_sieve
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hsq : ∀ I ∈ F, Squarefree I)
    (hchar : ∀ i : primePool F, ringChar (O ⧸ i.val) ≠ 2)
    (N : ℕ) (hN : 1 ≤ N) (hnorm : ∀ I ∈ F, Ideal.absNorm I ≤ N)
    (a : Ideal O → ℂ) (M : ℝ) (hM : 1 ≤ M) (R : Finset O)
    (hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M) :
    (∑ z ∈ R, ‖∑ I ∈ F, a I * (idealSexticRow F hFpos hFgood I z) ^ 3‖ ^ 2) ≤
      initialSieveConstant * (M + (N : ℝ) ^ 2) * ∑ I ∈ F, ‖a I‖ ^ 2 := by
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsupp : Set.InjOn (idealSupport F) (↑F : Set (Ideal O)) := by
    intro I hI J hJ h
    exact idealSupport_injective_on_squarefree F hI hJ (hsq I hI) (hsq J hJ) h
  have hNorm (I : Ideal O) (hI : I ∈ F) :
      supportNorm (fun i : primePool F => i.val) (idealSupport F I) ≤ (N : ℝ) := by
    unfold supportNorm
    rw [idealSupport_product_eq F hI (hsq I hI)]
    exact_mod_cast hnorm I hI
  have hb := quadratic_initial_finite_bound (fun i : primePool F => i.val)
    Subtype.val_injective (primePool_good F hFgood) hchar F (idealSupport F) hsupp
    (N : ℝ) (by positivity) hNorm a M hM R hR
  change (∑ z ∈ R, ‖∑ I ∈ F, a I * (idealSexticRow F hFpos hFgood I z) ^ 3‖ ^ 2) ≤
    (diagonalControl sieveCutoff * M + pvControl sieveCutoff * (N : ℝ) * F.card) *
      ∑ I ∈ F, ‖a I‖ ^ 2 at hb
  have hsub : F ⊆ idealsUpTo N := by
    intro I hI
    apply mem_idealsUpTo.mpr
    constructor
    · apply Nat.one_le_iff_ne_zero.mpr
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]
      exact hFpos I hI
    · exact hnorm I hI
  have hcardNat : F.card ≤ 64 * (N + 1) :=
    (Finset.card_le_card hsub).trans (CompactScaleBridge.idealsUpTo_card_le N)
  have hcard : (F.card : ℝ) ≤ 128 * (N : ℝ) := by
    have hh : (F.card : ℝ) ≤ 64 * ((N : ℝ) + 1) := by exact_mod_cast hcardNat
    linarith
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hdiag := diagonalControl_nonneg sieveCutoff
  have hpv := pvControl_nonneg sieveCutoff
  have hmul := mul_le_mul_of_nonneg_left hcard (mul_nonneg hpv (by positivity : (0 : ℝ) ≤ N))
  unfold initialSieveConstant
  nlinarith [mul_nonneg hdiag (sq_nonneg (N : ℝ)),
    mul_nonneg hpv (show 0 ≤ M by linarith)]

end QuadraticInitialBound

open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory

namespace CubicReflectionKernel

def gammaMultiplier (s : ℂ) : ℂ :=
  Complex.Gamma ((7 / 6 : ℂ) + s) * Complex.Gamma ((5 / 6 : ℂ) + s) /
    (Complex.Gamma ((7 / 6 : ℂ) - s) * Complex.Gamma ((5 / 6 : ℂ) - s))

theorem gammaMultiplier_neg (s : ℂ) : gammaMultiplier (-s) = (gammaMultiplier s)⁻¹ := by
  simp only [gammaMultiplier, sub_neg_eq_add, ← sub_eq_add_neg, inv_div]

theorem Gamma_vertical_ne_zero (a u : ℝ) (ha : 0 < a) :
    Complex.Gamma ((a : ℂ) + u * Complex.I) ≠ 0 := by
  apply Complex.Gamma_ne_zero_of_re_pos
  simpa using ha

theorem Gamma_vertical_conj (a u : ℝ) :
    Complex.Gamma ((a : ℂ) - u * Complex.I) =
      star (Complex.Gamma ((a : ℂ) + u * Complex.I)) := by
  change _ = (starRingEnd ℂ) (Complex.Gamma ((a : ℂ) + u * Complex.I))
  rw [← Complex.Gamma_conj]
  congr 1
  simp [sub_eq_add_neg]

theorem gammaMultiplier_norm_imaginary (u : ℝ) :
    ‖gammaMultiplier (u * Complex.I)‖ = 1 := by
  have ha := Gamma_vertical_ne_zero (7 / 6) u (by norm_num)
  have hb := Gamma_vertical_ne_zero (5 / 6) u (by norm_num)
  have hca := Gamma_vertical_conj (7 / 6) u
  have hcb := Gamma_vertical_conj (5 / 6) u
  push_cast at ha hb hca hcb
  rw [gammaMultiplier, hca, hcb, norm_div, norm_mul, norm_mul, norm_star, norm_star]
  exact div_self (mul_ne_zero (norm_ne_zero_iff.mpr ha) (norm_ne_zero_iff.mpr hb))

theorem Gamma_vertical_continuous (a : ℝ) (ha : 0 < a) :
    Continuous (fun u : ℝ => Complex.Gamma ((a : ℂ) + u * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  apply (Complex.continuousAt_Gamma _ ?_).comp
  · fun_prop
  · intro n hn
    have heq := congrArg Complex.re hn
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.neg_re, Complex.natCast_re] at heq
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

def axisMultiplier (u : ℝ) : ℂ := gammaMultiplier ((2 * Real.pi * u : ℝ) * Complex.I)

theorem axisMultiplier_norm (u : ℝ) : ‖axisMultiplier u‖ = 1 :=
  gammaMultiplier_norm_imaginary _

theorem axisMultiplier_continuous : Continuous axisMultiplier := by
  have h1 := (Gamma_vertical_continuous (7 / 6) (by norm_num)).comp
    (show Continuous (fun u : ℝ => 2 * Real.pi * u) by fun_prop)
  have h2 := (Gamma_vertical_continuous (5 / 6) (by norm_num)).comp
    (show Continuous (fun u : ℝ => 2 * Real.pi * u) by fun_prop)
  have h3 := (Gamma_vertical_continuous (7 / 6) (by norm_num)).comp
    (show Continuous (fun u : ℝ => -(2 * Real.pi * u)) by fun_prop)
  have h4 := (Gamma_vertical_continuous (5 / 6) (by norm_num)).comp
    (show Continuous (fun u : ℝ => -(2 * Real.pi * u)) by fun_prop)
  have hd := h3.mul h4
  have hne (u : ℝ) :
      Complex.Gamma ((7 / 6 : ℝ) + (-(2 * Real.pi * u) : ℝ) * Complex.I) *
      Complex.Gamma ((5 / 6 : ℝ) + (-(2 * Real.pi * u) : ℝ) * Complex.I) ≠ 0 :=
    mul_ne_zero (Gamma_vertical_ne_zero _ _ (by norm_num)) (Gamma_vertical_ne_zero _ _ (by norm_num))
  convert! (h1.mul h2).div hd hne using 1
  ext u
  simp only [axisMultiplier, gammaMultiplier, Function.comp_def, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg,
    Pi.div_apply, Pi.mul_apply]

def spectralProfile (logSource : SchwartzMap ℝ ℂ) (u : ℝ) : ℂ := axisMultiplier u * (𝓕 logSource) u

theorem spectralProfile_norm (logSource : SchwartzMap ℝ ℂ) (u : ℝ) :
    ‖spectralProfile logSource u‖ = ‖(𝓕 logSource) u‖ := by
  rw [spectralProfile, norm_mul, axisMultiplier_norm, one_mul]

theorem spectralProfile_continuous (logSource : SchwartzMap ℝ ℂ) : Continuous (spectralProfile logSource) :=
  axisMultiplier_continuous.mul (𝓕 logSource).continuous

theorem spectralProfile_moment_integrable (logSource : SchwartzMap ℝ ℂ) (j : ℕ) :
    Integrable (fun u : ℝ => ‖u‖ ^ j * ‖spectralProfile logSource u‖) := by
  simpa only [spectralProfile_norm] using (𝓕 logSource).integrable_pow_mul volume j

theorem spectralProfile_pow_integrable (logSource : SchwartzMap ℝ ℂ) (j : ℕ) :
    Integrable (fun u : ℝ => u ^ j • spectralProfile logSource u) := by
  apply (spectralProfile_moment_integrable logSource j).mono'
    ((show Continuous (fun u : ℝ => u ^ j • spectralProfile logSource u) by
      exact (continuous_id.pow j).smul (spectralProfile_continuous logSource)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun u => by simp only [norm_smul, norm_pow, le_rfl])

def reflectedLogProfile (logSource : SchwartzMap ℝ ℂ) : ℝ → ℂ := 𝓕 (spectralProfile logSource)

theorem reflectedLogProfile_smooth (logSource : SchwartzMap ℝ ℂ) :
    ContDiff ℝ ∞ (reflectedLogProfile logSource) :=
  Real.contDiff_fourier (fun j _ => spectralProfile_moment_integrable logSource j)

theorem reflectedLogProfile_deriv (logSource : SchwartzMap ℝ ℂ) (j : ℕ) :
    iteratedDeriv j (reflectedLogProfile logSource) =
      𝓕 (fun u : ℝ => (-2 * Real.pi * Complex.I * u) ^ j * spectralProfile logSource u) := by
  simpa only [reflectedLogProfile, smul_eq_mul] using
    (Real.iteratedDeriv_fourier (N := (⊤ : ℕ∞))
      (fun n _ => spectralProfile_pow_integrable logSource n) (by simp : (j : ℕ∞) ≤ ⊤))

end CubicReflectionKernel

end

end OAI

end


