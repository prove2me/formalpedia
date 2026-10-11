-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0057_1
-- name    : PNT_ZeroFree_433_0057_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T15:59:39.46336+00:00
-- url     : https://prove2.me/theorems/56a1450a-c12c-487a-bedd-015ea6e00350
-- title:
--   Zero-free region foundations: QuadraticSieve.MainTermDifference [0057_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.MainTermDifference
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/MainTermDifference.lean#L74-L356

import Definitions.Def_PNT_ZeroFree_433_0056

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/MainTermDifference.lean
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

open scoped BigOperators Classical
namespace QuadraticMainTermDifference
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic QuadraticDivisorCancellation QuadraticMainBoundary

theorem sum_powerset_disjoint_union {κ V : Type*} [DecidableEq κ] [AddCommMonoid V]
    (T G : Finset κ) (hTG : Disjoint T G) (f : Finset κ → V) :
    (∑ A ∈ (T ∪ G).powerset, f A) =
      ∑ H ∈ T.powerset, ∑ D ∈ G.powerset, f (H ∪ D) := by
  induction T using Finset.induction_on generalizing f with
  | empty => simp
  | @insert i T hi ih =>
    have hiG : i ∉ G := fun h => Finset.disjoint_left.mp hTG (by first | simp | exact_mod_cast le_top) h
    have hTG' : Disjoint T G := Finset.disjoint_of_subset_left (Finset.subset_insert _ _) hTG
    have hiU : i ∉ T ∪ G := by simp [hi, hiG]
    rw [Finset.insert_union, Finset.sum_powerset_insert hiU]
    rw [ih hTG' f, ih hTG' (fun A => f (insert i A))]
    rw [Finset.sum_powerset_insert hi]
    simp only [Finset.insert_union]

def normCutoff {κ : Type*} (q : κ → O) (K : ℝ) (A : Finset κ) : ℂ :=
  if (Ideal.absNorm (∏ i ∈ A, Ideal.span {q i}) : ℝ) ≤ K then 1 else 0

def partialSquarefreeSum {ι κ : Type*} [DecidableEq κ]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι)
    (q : κ → O) (K : ℝ) (V : Finset κ) : ℂ :=
  ∑ A ∈ V.powerset, normalizedRow P hg S (∏ i ∈ A, q i) * normCutoff q K A

def divisorSum {ι κ : Type*} [DecidableEq κ]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι)
    (q : κ → O) (G : Finset κ) : ℂ :=
  ∑ E ∈ G.powerset, (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {q i}) : ℂ) *
    normalizedRow P hg S (∏ i ∈ E, q i)

theorem actual_main_terms_difference {ι κ : Type*} [DecidableEq κ]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι)
    (q : κ → O) [∀ i, (Ideal.span {q i}).IsMaximal]
    (hprime : ∀ i, Prime (Ideal.span {q i}))
    (hinj : Function.Injective (fun i => (Ideal.span {q i} : Ideal O)))
    (T G : Finset κ) (hTG : Disjoint T G) (K : ℝ)
    (havoid : ∀ i ∈ G, ∀ j ∈ S, q i ∉ P j) :
    partialSquarefreeSum P hg S q K (T ∪ G) * divisorSum P hg S q G -
      partialSquarefreeSum P hg S q K T *
        (∏ i ∈ G, (1 - (1 : ℂ) / (Ideal.absNorm (Ideal.span {q i}) : ℂ))) =
      ∑ H ∈ T.powerset, ∑ D ∈ G.powerset, ∑ E ∈ G.powerset,
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {q i}) : ℂ) *
        normalizedRow P hg S ((∏ i ∈ H, q i) * (∏ i ∈ D, q i) * ∏ i ∈ E, q i) *
        (cutoffDifference K (∏ i ∈ H, Ideal.span {q i})
          (∏ i ∈ D, Ideal.span {q i}) : ℝ) := by
  have hdensity := actual_double_divisor_cancellation_coprime P hg S q hprime hinj
    G ∅ (by first | simp | exact_mod_cast le_top) havoid
  simp only [Finset.union_empty, Finset.powerset_empty, Finset.sum_singleton,
    Finset.prod_empty, UniqueFactorizationMonoid.moebius_one, Int.cast_one,
    normalizedRow_one, mul_one] at hdensity
  rw [← hdensity]
  unfold partialSquarefreeSum divisorSum
  rw [sum_powerset_disjoint_union T G hTG]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro H hH
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro D hD
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  have hHD : Disjoint H D := hTG.mono (Finset.mem_powerset.mp hH) (Finset.mem_powerset.mp hD)
  have hc : normCutoff q K (H ∪ D) - normCutoff q K H =
      (cutoffDifference K (∏ i ∈ H, Ideal.span {q i})
        (∏ i ∈ D, Ideal.span {q i}) : ℝ) := by
    simp only [normCutoff, Finset.prod_union hHD, cutoffDifference, Complex.ofReal_sub]
    split_ifs <;> norm_num
  simp only [Finset.prod_union hHD, normalizedRow_mul]
  rw [← hc]
  ring

end QuadraticMainTermDifference

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter
namespace CubicReflectionKernel

def realBeta (a b : ℝ) : ℝ :=
  ∫ x : ℝ in 0..1, x ^ (a - 1) * (1 - x) ^ (b - 1)

theorem realBeta_nonneg (a b : ℝ) : 0 ≤ realBeta a b := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x hx
  exact mul_nonneg (Real.rpow_nonneg hx.1 _) (Real.rpow_nonneg (sub_nonneg.mpr hx.2) _)

theorem betaIntegral_ofReal (a b : ℝ) :
    Complex.betaIntegral (a : ℂ) (b : ℂ) = (realBeta a b : ℂ) := by
  rw [Complex.betaIntegral, realBeta, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  dsimp only
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le,
    Complex.ofReal_cpow (sub_pos.mpr hx.2).le]
  push_cast
  rfl

theorem norm_betaIntegral_le (u v : ℂ) :
    ‖Complex.betaIntegral u v‖ ≤ realBeta u.re v.re := by
  apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)).trans_eq
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
  have hcast : (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr hx.2)]
  simp

theorem realBeta_eq_Gamma (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    realBeta a b = Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  apply Complex.ofReal_injective
  rw [← betaIntegral_ofReal]
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using ha) (by simpa using hb)]
  rw [← Complex.ofReal_add]
  simp only [Complex.Gamma_ofReal, Complex.ofReal_div, Complex.ofReal_mul]

theorem Gamma_ratio_eq_beta (z : ℂ) (d : ℝ) (hz : 0 < z.re) (hd : 0 < d) :
    Complex.Gamma z / Complex.Gamma (z + d) =
      Complex.betaIntegral z d / Complex.Gamma d := by
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hz (by simpa using hd)]
  have hdn : Complex.Gamma (d : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hd)
  field_simp

theorem Gamma_vertical_ratio_bound (a d t : ℝ) (ha : 0 < a) (hd : 0 < d) :
    ‖Complex.Gamma ((a : ℂ) + t * Complex.I) /
      Complex.Gamma ((a : ℂ) + t * Complex.I + d)‖ ≤
      Real.Gamma a / Real.Gamma (a + d) := by
  rw [Gamma_ratio_eq_beta _ d (by simpa using ha) hd, norm_div]
  have hg := Real.Gamma_pos_of_pos hd
  have hb := norm_betaIntegral_le ((a : ℂ) + t * Complex.I) (d : ℂ)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero] at hb
  rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg]
  calc
    _ ≤ realBeta a d / Real.Gamma d := div_le_div_of_nonneg_right hb hg.le
    _ = _ := by rw [realBeta_eq_Gamma a d ha hd]; field_simp

theorem inverse_Gamma_shift (z : ℂ) (n : ℕ) :
    (Complex.Gamma z)⁻¹ =
      (∏ k ∈ Finset.range n, (z + k)) * (Complex.Gamma (z + n))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (z + n),
      Finset.prod_range_succ]
    push_cast
    ring_nf

theorem Gamma_shifted_pair_bound (a σ t : ℝ) (n : ℕ)
    (ha : 0 < a + σ) (hd : 0 < (n : ℝ) - 2 * σ) :
    ‖Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
      Complex.Gamma ((a : ℂ) - (σ + t * Complex.I) + n)‖ ≤
      Real.Gamma (a + σ) / Real.Gamma (a - σ + n) := by
  have hb := Gamma_vertical_ratio_bound (a + σ) ((n : ℝ) - 2 * σ) t ha hd
  have hn : ((a + σ : ℝ) : ℂ) + t * Complex.I =
      (a : ℂ) + (σ + t * Complex.I) := by push_cast; ring
  have hdp : ((a + σ : ℝ) : ℂ) + t * Complex.I + ((n : ℝ) - 2 * σ : ℝ) =
      ((a - σ + n : ℝ) : ℂ) + t * Complex.I := by push_cast; ring
  have hdm : (a : ℂ) - (σ + t * Complex.I) + n =
      ((a - σ + n : ℝ) : ℂ) - t * Complex.I := by push_cast; ring
  have hr : a + σ + ((n : ℝ) - 2 * σ) = a - σ + n := by ring
  rw [hdp, hn, hr] at hb
  rw [hdm, Gamma_vertical_conj, norm_div, norm_star]
  simpa only [norm_div] using hb

theorem gammaMultiplier_left_bound (t : ℝ) :
    ‖gammaMultiplier ((-(1 / 4) : ℝ) + t * Complex.I)‖ ≤
      (Real.Gamma (11 / 12) / Real.Gamma (17 / 12)) *
      (Real.Gamma (7 / 12) / Real.Gamma (13 / 12)) := by
  have h1 := Gamma_shifted_pair_bound (7 / 6) (-(1 / 4)) t 0 (by norm_num) (by norm_num)
  have h2 := Gamma_shifted_pair_bound (5 / 6) (-(1 / 4)) t 0 (by norm_num) (by norm_num)
  norm_num only [Nat.cast_zero, add_zero, show (7 / 6 : ℝ) + -(1 / 4) = 11 / 12 by norm_num,
    show (7 / 6 : ℝ) - -(1 / 4) = 17 / 12 by norm_num,
    show (5 / 6 : ℝ) + -(1 / 4) = 7 / 12 by norm_num,
    show (5 / 6 : ℝ) - -(1 / 4) = 13 / 12 by norm_num] at h1 h2
  have heq : gammaMultiplier ((-(1 / 4) : ℝ) + t * Complex.I) =
      (Complex.Gamma (((7 / 6 : ℝ) : ℂ) + ((-(1 / 4) : ℝ) + t * Complex.I)) /
       Complex.Gamma (((7 / 6 : ℝ) : ℂ) - ((-(1 / 4) : ℝ) + t * Complex.I))) *
      (Complex.Gamma (((5 / 6 : ℝ) : ℂ) + ((-(1 / 4) : ℝ) + t * Complex.I)) /
       Complex.Gamma (((5 / 6 : ℝ) : ℂ) - ((-(1 / 4) : ℝ) + t * Complex.I))) := by
    simp only [gammaMultiplier, Complex.ofReal_div, Complex.ofReal_ofNat]
    exact div_mul_div_comm _ _ _ _ |>.symm
  rw [heq, norm_mul]
  exact mul_le_mul h1 h2 (norm_nonneg _) (div_nonneg
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 11 / 12)).le
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 17 / 12)).le)

theorem norm_Gamma_shift_factor (z : ℂ) (n : ℕ) :
    ‖∏ k ∈ Finset.range n, (z + k)‖ ≤ (‖z‖ + n) ^ n := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _k ∈ Finset.range n, (‖z‖ + n) := by
      apply Finset.prod_le_prod
      · intro k hk
        exact norm_nonneg _
      · intro k hk
        have hk' : (k : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hk).le
        exact (norm_add_le _ _).trans (by simpa using add_le_add_left hk' ‖z‖)
    _ = _ := by simp

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

theorem Gamma_pair_strip_bound (a : ℝ) (ha : 1 / 4 < a) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
        Complex.Gamma ((a : ℂ) - (σ + t * Complex.I))‖ ≤
        C * (1 + |t|) ^ (2 * A + 2) := by
  let n : ℕ := 2 * A + 2
  let I : Set ℝ := Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)
  have hapos (σ : ℝ) (hσ : σ ∈ I) : 0 < a + σ := by
    have := hσ.1
    linarith
  have hdpos (σ : ℝ) (hσ : σ ∈ I) : 0 < (n : ℝ) - 2 * σ := by
    have := hσ.2
    dsimp [n]
    push_cast
    linarith
  have hdenpos (σ : ℝ) (hσ : σ ∈ I) : 0 < a - σ + n := by
    have h1 := hapos σ hσ
    have h2 := hdpos σ hσ
    linarith
  have hc1 : ContinuousOn (fun σ : ℝ => Real.Gamma (a + σ)) I :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp
      (continuous_const.add continuous_id).continuousOn hapos
  have hc2 : ContinuousOn (fun σ : ℝ => Real.Gamma (a - σ + n)) I :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp
      ((continuous_const.sub continuous_id).add continuous_const).continuousOn hdenpos
  have hc : ContinuousOn (fun σ : ℝ => Real.Gamma (a + σ) / Real.Gamma (a - σ + n)) I :=
    hc1.div hc2 (fun σ hσ => (Real.Gamma_pos_of_pos (hdenpos σ hσ)).ne')
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc : IsCompact I).bddAbove_image hc
  let C₁ : ℝ := |C₀| + 1
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  have hreal (σ : ℝ) (hσ : σ ∈ I) :
      Real.Gamma (a + σ) / Real.Gamma (a - σ + n) ≤ C₁ := by
    exact (hC₀ (Set.mem_image_of_mem _ hσ)).trans (by dsimp [C₁]; linarith [le_abs_self C₀])
  let B : ℝ := |a| + A + 1 + n + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B ^ n * C₁, mul_pos (pow_pos hB n) hC₁, ?_⟩
  intro σ hσ t
  have hσ' : σ ∈ I := hσ
  have hσabs : |σ| ≤ (A : ℝ) + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hσ.1, hσ.2, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  have hz : ‖(a : ℂ) - (σ + t * Complex.I)‖ ≤ |a| + A + 1 + |t| := by
    calc
      _ ≤ ‖(a : ℂ)‖ + ‖(σ : ℂ) + t * Complex.I‖ := norm_sub_le _ _
      _ ≤ ‖(a : ℂ)‖ + (‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖) :=
        add_le_add le_rfl (norm_add_le _ _)
      _ = |a| + (|σ| + |t|) := by simp
      _ ≤ _ := by linarith
  have hzB : ‖(a : ℂ) - (σ + t * Complex.I)‖ + n ≤ B * (1 + |t|) := by
    dsimp [B]
    nlinarith [abs_nonneg a, abs_nonneg t, (Nat.cast_nonneg A : (0 : ℝ) ≤ A), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hprod : ‖∏ k ∈ Finset.range n, ((a : ℂ) - (σ + t * Complex.I) + k)‖ ≤
      B ^ n * (1 + |t|) ^ n := by
    apply (norm_Gamma_shift_factor _ n).trans
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hzB n
  have hratio := (Gamma_shifted_pair_bound a σ t n (hapos σ hσ') (hdpos σ hσ')).trans
    (hreal σ hσ')
  have heq : Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
      Complex.Gamma ((a : ℂ) - (σ + t * Complex.I)) =
      (∏ k ∈ Finset.range n, ((a : ℂ) - (σ + t * Complex.I) + k)) *
      (Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
       Complex.Gamma ((a : ℂ) - (σ + t * Complex.I) + n)) := by
    rw [div_eq_mul_inv, inverse_Gamma_shift _ n, div_eq_mul_inv]
    ring
  rw [heq, norm_mul]
  calc
    _ ≤ (B ^ n * (1 + |t|) ^ n) * C₁ :=
      mul_le_mul hprod hratio (norm_nonneg _) (by positivity)
    _ = _ := by dsimp [n]; ring


end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel


end CubicReflectionKernel

end

end OAI

end


