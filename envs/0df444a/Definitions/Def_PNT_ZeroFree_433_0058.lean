-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0058
-- name    : PNT_ZeroFree_433_0058
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T16:02:42.056186+00:00
-- url     : https://prove2.me/theorems/7c09c9f2-d401-4110-b2fb-51a0e5f9e10e
-- title:
--   Zero-free region foundations: Mellin.InverseContour [0058]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Mellin.InverseContour
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Mellin/InverseContour.lean#L76-L668

import Definitions.Def_PNT_ZeroFree_433_0057

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Mellin/InverseContour.lean#L76-L668
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Mellin.InverseContour
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

def inverseMellinIntegrand (V : ℝ → ℂ) (j : ℕ) (y : ℝ) (s : ℂ) : ℂ :=
  (y : ℂ) ^ (-s) * mellinEulerData V j s

theorem inverseMellinIntegrand_differentiableAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (j : ℕ) (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (inverseMellinIntegrand V j y) s := by
  exact (differentiableAt_id.neg.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).mul
    (mellinEulerData_differentiableAt V a b ha hsupp hV j s hs)

theorem inverseMellinIntegrand_vertical_integrable
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ))
    (y : ℝ) (hy : 0 < y) :
    Integrable (fun t : ℝ => inverseMellinIntegrand V j y ((σ : ℂ) + t * Complex.I)) := by
  apply (mellinEulerData_vertical_integrable V a b ha hsupp hV A j σ hσ).bdd_mul
    (c := y ^ (-σ))
  · exact ((show Continuous (fun t : ℝ => -((σ : ℂ) + t * Complex.I)) by fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp

theorem inverseMellinIntegrand_strip_bound
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (y : ℝ) (hy : 0 < y) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖inverseMellinIntegrand V j y ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨C, hC, hb⟩ := mellinEulerData_strip_bound V a b ha hsupp hV A j
  have hc : Continuous (fun σ : ℝ => y ^ (-σ)) :=
    (Real.continuous_const_rpow hy.ne').comp continuous_neg
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Set.Icc (-(1 / 4 : ℝ)) (A : ℝ))).bddAbove_image hc.continuousOn
  refine ⟨(|B| + 1) * C, by positivity, ?_⟩
  intro σ hσ t
  have hby : y ^ (-σ) ≤ |B| + 1 :=
    (hB (Set.mem_image_of_mem _ hσ)).trans (by linarith [le_abs_self B])
  rw [inverseMellinIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
  calc
    _ ≤ (|B| + 1) * (C / (1 + t ^ 2)) :=
      mul_le_mul hby (hb σ hσ t) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem mellinInv_euler_shift
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ))
    (y : ℝ) (hy : 0 < y) :
    mellinInv 0 (mellinEulerData V j) y = mellinInv σ (mellinEulerData V j) y := by
  obtain ⟨C, hC, hb⟩ := inverseMellinIntegrand_strip_bound V a b ha hsupp hV A j y hy
  have h0 : (0 : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ) := by
    constructor
    · norm_num
    · exact Nat.cast_nonneg A
  have hshift (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)) :
      (∫ t : ℝ, inverseMellinIntegrand V j y ((-(1 / 4) : ℝ) + t * Complex.I)) =
      ∫ t : ℝ, inverseMellinIntegrand V j y ((ρ : ℂ) + t * Complex.I) := by
    apply VerticalContourShift.integral_eq_of_strip_decay
      (inverseMellinIntegrand V j y) (-(1 / 4)) ρ C hρ.1
    · intro z hzlo hzhi
      apply inverseMellinIntegrand_differentiableAt V a b ha hsupp hV j y hy z
      linarith
    · apply inverseMellinIntegrand_vertical_integrable V a b ha hsupp hV A j
        (-(1 / 4)) ⟨le_rfl, hρ.1.trans hρ.2⟩ y hy
    · exact inverseMellinIntegrand_vertical_integrable V a b ha hsupp hV A j ρ hρ y hy
    · intro r hr t
      exact hb r ⟨hr.1, hr.2.trans hρ.2⟩ t
  have heq := (hshift 0 h0).symm.trans (hshift σ hσ)
  simpa only [mellinInv, smul_eq_mul, inverseMellinIntegrand] using
    congrArg (fun z : ℂ => (1 / (2 * Real.pi) : ℝ) • z) heq

theorem mellinInv_euler_line_bound
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ),
      ∀ y : ℝ, 0 < y → ‖mellinInv σ (mellinEulerData V j) y‖ ≤ C * y ^ (-σ) := by
  obtain ⟨C, hC, hb⟩ := mellinEulerData_strip_bound V a b ha hsupp hV A j
  refine ⟨C / 2, by positivity, ?_⟩
  intro σ hσ y hy
  have hint : ‖∫ t : ℝ, (y : ℂ) ^ (-((σ : ℂ) + t * Complex.I)) *
        mellinEulerData V j ((σ : ℂ) + t * Complex.I)‖ ≤
      (y ^ (-σ) * C) * Real.pi := by
    calc
      _ ≤ ∫ t : ℝ, (y ^ (-σ) * C) * (1 + t ^ 2)⁻¹ := by
        apply norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _)
        filter_upwards [] with t
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
        simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
        simpa only [div_eq_mul_inv, mul_assoc] using
          mul_le_mul_of_nonneg_left (hb σ hσ t) (Real.rpow_nonneg hy.le (-σ))
      _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  rw [mellinInv, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  simp only [smul_eq_mul]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ((y ^ (-σ) * C) * Real.pi) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by field_simp

def paperEulerKernel (V : ℝ → ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  mellinInv 0 (mellinEulerData V j) (paperScale * x)

theorem mellinEulerData_axis (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hlog : ∀ u, logSource u = V (Real.exp u)) (j : ℕ) (u : ℝ) :
    mellinEulerData V j (2 * Real.pi * u * Complex.I) =
      (-2 * Real.pi * Complex.I * u) ^ j * spectralProfile logSource u := by
  have hu : (2 * Real.pi * u * Complex.I : ℂ) =
      ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [mellinEulerData, mellinData, hu, mellin_axis_eq_fourier V logSource hlog]
  have hb : -(((2 * Real.pi * u : ℝ) : ℂ) * Complex.I) =
      -2 * Real.pi * Complex.I * u := by push_cast; ring
  rw [hb, spectralProfile, axisMultiplier]
  ring

theorem paperEulerKernel_eq_euler (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hlog : ∀ u, logSource u = V (Real.exp u)) (j : ℕ) (x : ℝ) (hx : 0 < x) :
    paperEulerKernel V j x = LocalLogFourier.eulerDeriv (paperKernel V) j x := by
  rw [paperKernel_euler_eq V logSource hlog j x hx, reflectedLogProfile_deriv]
  unfold paperEulerKernel
  rw [mellinInv_eq_fourierInv 0 _ (mul_pos paperScale_pos hx)]
  simp only [Complex.ofReal_zero, neg_zero, Complex.cpow_zero, one_smul,
    Real.fourierInv_eq_fourier_neg, neg_neg, zero_add]
  have hfun : (fun u : ℝ => mellinEulerData V j (2 * Real.pi * u * Complex.I)) =
      (fun u : ℝ => (-2 * Real.pi * Complex.I * u) ^ j * spectralProfile logSource u) := by
    funext u
    exact mellinEulerData_axis V logSource hlog j u
  rw [hfun]

theorem paperKernel_euler_decay_at_line
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x →
      ‖LocalLogFourier.eulerDeriv (paperKernel V) j x‖ ≤ C * x ^ (-σ) := by
  obtain ⟨C, hC, hb⟩ := mellinInv_euler_line_bound V a b ha hsupp hV A j
  refine ⟨C * paperScale ^ (-σ), mul_pos hC (Real.rpow_pos_of_pos paperScale_pos _), ?_⟩
  intro x hx
  rw [← paperEulerKernel_eq_euler V (logSchwartz V a b ha hsupp hV) (by intro u; rfl) j x hx]
  unfold paperEulerKernel
  rw [mellinInv_euler_shift V a b ha hsupp hV A j σ hσ _ (mul_pos paperScale_pos hx)]
  have hbound := hb σ hσ (paperScale * x) (mul_pos paperScale_pos hx)
  rw [Real.mul_rpow paperScale_pos.le hx.le] at hbound
  simpa only [mul_assoc] using hbound

theorem paperKernel_euler_power_decay
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x →
      (‖LocalLogFourier.eulerDeriv (paperKernel V) j x‖ ≤ C * x ^ (1 / 4 : ℝ)) ∧
      (‖LocalLogFourier.eulerDeriv (paperKernel V) j x‖ ≤ C * x ^ (-(A : ℝ))) := by
  have hleft : -(1 / 4 : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ) := by
    constructor
    · rfl
    · linarith [show (0 : ℝ) ≤ A from Nat.cast_nonneg A]
  have hright : (A : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ) := by
    constructor
    · linarith [show (0 : ℝ) ≤ A from Nat.cast_nonneg A]
    · rfl
  obtain ⟨CL, hCL, hL⟩ := paperKernel_euler_decay_at_line V a b ha hsupp hV A j _ hleft
  obtain ⟨CR, hCR, hR⟩ := paperKernel_euler_decay_at_line V a b ha hsupp hV A j _ hright
  refine ⟨max CL CR, lt_of_lt_of_le hCL (le_max_left _ _), ?_⟩
  intro x hx
  constructor
  · have hh : ‖LocalLogFourier.eulerDeriv (paperKernel V) j x‖ ≤ CL * x ^ (1 / 4 : ℝ) := by
      simpa only [neg_neg] using hL x hx
    exact hh.trans
      (mul_le_mul_of_nonneg_right (le_max_left CL CR) (Real.rpow_nonneg hx.le _))
  · exact (hR x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_right CL CR) (Real.rpow_nonneg hx.le _))

theorem paperKernel_euler_uniform_weighted_bound
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i ≤ K, ∀ x : ℝ, 0 < x →
      (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperKernel V) i x‖ ≤ C := by
  choose c hc hb using fun i : Fin (K + 1) =>
    paperKernel_euler_power_decay V a b ha hsupp hV A i.val
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
  have hsmall : ∀ i ≤ K, ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖LocalLogFourier.eulerDeriv (paperKernel V) i x‖ ≤ D := by
    intro i hi x hx hx1
    let k : Fin (K + 1) := ⟨i, by omega⟩
    have hp : x ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hx.le hx1 (by norm_num)
    calc
      _ ≤ c k * x ^ (1 / 4 : ℝ) := (hb k x hx).1
      _ ≤ c k := by simpa using mul_le_mul_of_nonneg_left hp (hc k).le
      _ ≤ D := hci k
  have hlarge : ∀ i ≤ K, ∀ x : ℝ, 1 ≤ x →
      x ^ A * ‖LocalLogFourier.eulerDeriv (paperKernel V) i x‖ ≤ D := by
    intro i hi x hx1
    have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    let k : Fin (K + 1) := ⟨i, by omega⟩
    have hxpow : x ^ A ≠ 0 := pow_ne_zero A hx.ne'
    calc
      _ ≤ x ^ A * (c k * x ^ (-(A : ℝ))) :=
        mul_le_mul_of_nonneg_left (hb k x hx).2 (pow_nonneg hx.le A)
      _ = c k := by
        rw [Real.rpow_neg hx.le, Real.rpow_natCast]
        field_simp
      _ ≤ D := hci k
  refine ⟨2 ^ A * (D + D), by positivity, ?_⟩
  intro i hi x hx
  exact LocalLogFourier.euler_two_regime_bound (paperKernel V) A K D D hD.le hD.le
    hsmall hlarge i hi x hx

end CubicReflectionKernel

namespace DescentFiberCost
open scoped BigOperators Classical
open ConcretePrimeRowBridge

abbrev O := ActualEisensteinCubic.O

theorem finite_ideal_count_real (s : Finset (Ideal O)) (H : ℝ) (hH : 1 ≤ H)
    (hpos : ∀ I ∈ s, I ≠ ⊥) (hN : ∀ I ∈ s, (Ideal.absNorm I : ℝ) ≤ H) :
    (s.card : ℝ) ≤ 128 * H := by
  have hs : s ⊆ idealsUpTo ⌊H⌋₊ := by
    intro I hI
    apply mem_idealsUpTo.mpr
    refine ⟨?_, Nat.le_floor (hN I hI)⟩
    exact Nat.one_le_iff_ne_zero.mpr (fun h => hpos I hI (Ideal.absNorm_eq_zero_iff.mp h))
  have hc := (Finset.card_le_card hs).trans (CompactScaleBridge.idealsUpTo_card_le ⌊H⌋₊)
  have hfloor : (⌊H⌋₊ : ℝ) ≤ H := Nat.floor_le (by linarith)
  have hr : (s.card : ℝ) ≤ 64 * ((⌊H⌋₊ : ℝ) + 1) := by exact_mod_cast hc
  linarith

theorem fixed_triple_count
    (s : Finset (Ideal O × Ideal O × Ideal O)) (B T W : ℝ)
    (hB : 1 ≤ B) (hT : 1 ≤ T) (hW : 1 ≤ W)
    (hpos : ∀ x ∈ s, x.1 ≠ ⊥ ∧ x.2.1 ≠ ⊥ ∧ x.2.2 ≠ ⊥)
    (hN : ∀ x ∈ s, (Ideal.absNorm x.1 : ℝ) ≤ B ∧
      (Ideal.absNorm x.2.1 : ℝ) ≤ T ∧ (Ideal.absNorm x.2.2 : ℝ) ≤ W) :
    (s.card : ℝ) ≤ 128 ^ 3 * B * T * W := by
  let a := s.image Prod.fst
  let b := s.image (fun x => x.2.1)
  let c := s.image (fun x => x.2.2)
  have hsub : s ⊆ a ×ˢ (b ×ˢ c) := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩,
        Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩⟩
  have ha : (a.card : ℝ) ≤ 128 * B := by
    apply finite_ideal_count_real a B hB
    · intro I hI
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hI
      exact (hpos x hx).1
    · intro I hI
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hI
      exact (hN x hx).1
  have hb : (b.card : ℝ) ≤ 128 * T := by
    apply finite_ideal_count_real b T hT
    · intro I hI
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hI
      exact (hpos x hx).2.1
    · intro I hI
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hI
      exact (hN x hx).2.1
  have hc : (c.card : ℝ) ≤ 128 * W := by
    apply finite_ideal_count_real c W hW
    · intro I hI
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hI
      exact (hpos x hx).2.2
    · intro I hI
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hI
      exact (hN x hx).2.2
  have hs : (s.card : ℝ) ≤ (a.card : ℝ) * ((b.card : ℝ) * c.card) := by
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_product] at hcard
    exact_mod_cast hcard
  apply hs.trans
  calc
    _ ≤ (128 * B) * ((128 * T) * (128 * W)) := by gcongr
    _ = _ := by ring

theorem complete_second_prefactor
    (K ell B F A C d J g e v t w c : ℝ)
    (hK : K ≠ 0) (hell : ell ≠ 0) (hB : B ≠ 0) (hF : F ≠ 0)
    (hC : C ≠ 0) (hd : d ≠ 0) (hJ : J ≠ 0)
    (hg : g ≠ 0) (he : e ≠ 0) (hv : v ≠ 0) (hc : c ≠ 0)
    (Li : ℝ) (hLi : Li ≠ 0) :
    (K * A * C / (d * ell ^ 2 * B ^ 2 * F * c)) *
      ((ell ^ 2 * B ^ 4 * F ^ 2 * d / (K * C ^ 2 * J)) * g / (e * Li)) *
      ((B * c / J) * t * w) *
      ((Li / (g * v)) * (J * C * e * v)) =
      (B * F * A * t * w) * B ^ 2 / J := by
  field_simp

theorem complete_second_zero_prefactor
    (K ell B F A C d J t c : ℝ)
    (hK : K ≠ 0) (hell : ell ≠ 0) (hB : B ≠ 0) (hF : F ≠ 0)
    (hA : A ≠ 0) (hC : C ≠ 0) (hd : d ≠ 0) (hJ : J ≠ 0)
    (ht : t ≠ 0) (hc : c ≠ 0) :
    (K * A * C / (d * ell ^ 2 * B ^ 2 * F * c)) *
      ((ell ^ 2 * B ^ 4 * F ^ 2 * d / (K * C ^ 2 * J)) * (ell / (A * C * t))) *
      (C * t) * (B * c) = (ell * B ^ 3) * F / (C * J) := by
  field_simp

end DescentFiberCost

namespace EisensteinSchwartzPoisson
open MeasureTheory Set
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem fourier_real_line_integrable (f : 𝓢(ℂ, ℂ)) :
    Integrable (fun x : ℝ => 𝓕 (f : ℂ → ℂ) (x : ℂ)) := by
  have h : Integrable (fun x : ℝ => horizontalSlice (𝓕 f) 0 x) :=
    (horizontalSlice (𝓕 f) 0).integrable
  simpa only [horizontalSlice_apply, complexPoint_eq, mul_zero, add_zero,
    Complex.ofReal_zero, SchwartzMap.fourier_coe] using h

theorem fourier_real_line_integral (f : 𝓢(ℂ, ℂ)) :
    (∫ x : ℝ, 𝓕 (f : ℂ → ℂ) (x : ℂ)) =
      ∫ y : ℝ, f (Complex.I * (y : ℂ)) := by
  let g : ℝ → ℂ := partialFourier f 0
  have hF : 𝓕 g = fun x : ℝ => 𝓕 (f : ℂ → ℂ) (x : ℂ) := by
    funext x
    simpa only [g, complexPoint_eq, Complex.ofReal_zero, mul_zero, add_zero] using fourier_partialFourier f x 0
  have hgi : Integrable (𝓕 g) := by rw [hF]; exact fourier_real_line_integrable f
  have hinv : 𝓕⁻ (𝓕 g) (0 : ℝ) = g 0 :=
    (partialFourier_integrable f 0).fourierInv_fourier_eq hgi
      (partialFourier_continuous f 0).continuousAt
  calc
    _ = ∫ x : ℝ, 𝓕 g x := by rw [hF]
    _ = 𝓕⁻ (𝓕 g) 0 := by simp [Real.fourierInv_eq]
    _ = g 0 := hinv
    _ = _ := by simp [g, partialFourier_eq_integral, complexPoint_eq]

theorem paperFrequency_imaginary (x : ℝ) :
    paperFrequency ((x : ℂ) * Complex.I) = (((2 / Real.sqrt 3) * x : ℝ) : ℂ) := by
  simp [paperFrequency]
  ring_nf
  simp

theorem paperRadialFourier_square (W : ℝ → ℂ) (x : ℝ) :
    paperRadialFourier W (x ^ 2) =
      (2 / Real.sqrt 3 : ℝ) • 𝓕 (fun z : ℂ => W (‖z‖ ^ 2))
        ((((2 / Real.sqrt 3) * x : ℝ) : ℂ)) := by
  have h := paperFourier_radial W ((x : ℂ) * Complex.I)
  have hn : ‖(x : ℂ) * Complex.I‖ ^ 2 = x ^ 2 := by
    simp [ Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hn, paperFourier_eq_standard, paperFrequency_imaginary] at h
  exact h.symm

theorem radial_square_integrable (W : 𝓢(ℝ, ℂ)) :
    Integrable (fun x : ℝ => W (x ^ 2)) := by
  have h : Integrable (fun x : ℝ => horizontalSlice (radialTest W) 0 x) :=
    (horizontalSlice (radialTest W) 0).integrable
  simpa [horizontalSlice_apply, complexPoint_eq, radialTest_apply,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

theorem paperRadialFourier_square_integrable (W : 𝓢(ℝ, ℂ)) :
    Integrable (fun x : ℝ => paperRadialFourier W (x ^ 2)) := by
  have he : (radialTest W : ℂ → ℂ) = fun z : ℂ => W (‖z‖ ^ 2) := rfl
  have hc : (2 / Real.sqrt 3 : ℝ) ≠ 0 := by positivity
  have h := ((fourier_real_line_integrable (radialTest W)).comp_mul_left' hc).smul
    (2 / Real.sqrt 3 : ℝ)
  change Integrable (fun x : ℝ => (2 / Real.sqrt 3 : ℝ) •
    𝓕 (radialTest W : ℂ → ℂ) ((((2 / Real.sqrt 3) * x : ℝ) : ℂ))) at h
  simpa only [paperRadialFourier_square, he] using h

theorem paperRadialFourier_square_integral (W : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ, paperRadialFourier W (x ^ 2)) = ∫ x : ℝ, W (x ^ 2) := by
  have hc : (0 : ℝ) < 2 / Real.sqrt 3 := by positivity
  have he : (radialTest W : ℂ → ℂ) = fun z : ℂ => W (‖z‖ ^ 2) := rfl
  calc
    _ = (2 / Real.sqrt 3 : ℝ) •
        ∫ x : ℝ, 𝓕 (radialTest W : ℂ → ℂ) ((((2 / Real.sqrt 3) * x : ℝ) : ℂ)) := by
      simp only [paperRadialFourier_square, he, integral_smul]
    _ = ∫ x : ℝ, 𝓕 (radialTest W : ℂ → ℂ) (x : ℂ) := by
      rw [Measure.integral_comp_mul_left
        (fun x : ℝ => 𝓕 (radialTest W : ℂ → ℂ) (x : ℂ)) (2 / Real.sqrt 3)]
      rw [abs_of_pos (inv_pos.mpr hc), smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    _ = ∫ y : ℝ, radialTest W (Complex.I * (y : ℂ)) := fourier_real_line_integral _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp [radialTest_apply,  Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem integral_even_eq_twice_Ioi (F : ℝ → ℂ) (hF : Integrable F)
    (heven : ∀ x : ℝ, F (-x) = F x) :
    (∫ x : ℝ, F x) = 2 * ∫ x : ℝ in Ioi 0, F x := by
  have hneg : (∫ x : ℝ in Iic 0, F x) = ∫ x : ℝ in Ioi 0, F x := by
    calc
      _ = ∫ x : ℝ in Ioi 0, F (-x) := by simp
      _ = _ := setIntegral_congr_fun measurableSet_Ioi (fun x _ => heven x)
  rw [← integral_add_compl (s := Ioi 0) measurableSet_Ioi hF, compl_Ioi, hneg]
  ring

theorem paperRadialFourier_halfline_integral (W : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ in Ioi 0, paperRadialFourier W (x ^ 2)) =
      ∫ x : ℝ in Ioi 0, W (x ^ 2) := by
  have h := paperRadialFourier_square_integral W
  rw [integral_even_eq_twice_Ioi _ (paperRadialFourier_square_integrable W)
    (by intro x; simp), integral_even_eq_twice_Ioi _ (radial_square_integrable W)
    (by intro x; simp)] at h
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h

end EisensteinSchwartzPoisson

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

def logRadius (a b : ℝ) : ℝ := |Real.log a| + |Real.log b| + 1

theorem logRadius_pos (a b : ℝ) : 0 < logRadius a b := by unfold logRadius; positivity

def logCutoff (a b : ℝ) : ContDiffBump (0 : ℝ) where
  rIn := logRadius a b
  rOut := logRadius a b + 1
  rIn_pos := logRadius_pos a b
  rIn_lt_rOut := by linarith

def logOuterCutoff (a b : ℝ) : ContDiffBump (0 : ℝ) where
  rIn := logRadius a b + 1
  rOut := logRadius a b + 2
  rIn_pos := by have := logRadius_pos a b; linarith
  rIn_lt_rOut := by linarith

def expCorrection (a b u : ℝ) : ℝ := logOuterCutoff a b u * (Real.exp u - u)
def patchedExp (a b u : ℝ) : ℝ := u + expCorrection a b u

theorem expCorrection_compact (a b : ℝ) : HasCompactSupport (expCorrection a b) :=
  (logOuterCutoff a b).hasCompactSupport.mul_right

theorem expCorrection_smooth (a b : ℝ) : ContDiff ℝ ∞ (expCorrection a b) :=
  (logOuterCutoff a b).contDiff.mul (Real.contDiff_exp.sub contDiff_id)

theorem patchedExp_temperate (a b : ℝ) : Function.HasTemperateGrowth (patchedExp a b) :=
  Function.HasTemperateGrowth.id'.add ((expCorrection_compact a b).hasTemperateGrowth
    (expCorrection_smooth a b))

theorem patchedExp_proper (a b : ℝ) :
    ∃ (k : ℕ) (C : ℝ), ∀ u : ℝ, ‖u‖ ≤ C * (1 + ‖patchedExp a b u‖) ^ k := by
  obtain ⟨u₀, hu₀⟩ := (expCorrection_smooth a b).continuous.norm.exists_forall_ge_of_hasCompactSupport
    (expCorrection_compact a b).norm
  refine ⟨1, ‖expCorrection a b u₀‖ + 1, ?_⟩
  intro u
  have htriangle : ‖u‖ ≤ ‖patchedExp a b u‖ + ‖expCorrection a b u‖ := by
    simpa only [patchedExp, add_sub_cancel_right] using
      norm_sub_le (patchedExp a b u) (expCorrection a b u)
  have hbound := hu₀ u
  simp only [pow_one]
  nlinarith [norm_nonneg (patchedExp a b u), norm_nonneg (expCorrection a b u₀)]

def logPullbackCLM (a b : ℝ) : SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.smulLeftCLM ℂ (logCutoff a b)).comp
    (SchwartzMap.compCLM ℝ (patchedExp_temperate a b) (patchedExp_proper a b))

theorem logPullbackCLM_apply (a b : ℝ) (W : SchwartzMap ℝ ℂ) (u : ℝ) :
    logPullbackCLM a b W u = logCutoff a b u • W (patchedExp a b u) := by
  rw [logPullbackCLM, ContinuousLinearMap.comp_apply, SchwartzMap.smulLeftCLM_apply_apply
    ((logCutoff a b).hasCompactSupport.hasTemperateGrowth (logCutoff a b).contDiff)]
  rfl

theorem logCutoff_eq_one_of_source (a b : ℝ) (ha : 0 < a) (u : ℝ)
    (hu : Real.exp u ∈ Set.Icc a b) : logCutoff a b u = 1 := by
  apply (logCutoff a b).one_of_mem_closedBall
  have hl := Real.log_le_log ha hu.1
  have hr := Real.log_le_log (Real.exp_pos u) hu.2
  simp only [Real.log_exp] at hl hr
  change dist u 0 ≤ logRadius a b
  rw [Real.dist_eq, sub_zero]
  apply abs_le.mpr
  constructor <;> dsimp [logRadius] <;>
    linarith [neg_abs_le (Real.log a), le_abs_self (Real.log b), abs_nonneg (Real.log a), abs_nonneg (Real.log b)]

theorem patchedExp_eq_exp_of_cutoff_ne_zero (a b u : ℝ) (hu : logCutoff a b u ≠ 0) :
    patchedExp a b u = Real.exp u := by
  have hmem : u ∈ Function.support (logCutoff a b) := hu
  rw [(logCutoff a b).support_eq] at hmem
  have heta : logOuterCutoff a b u = 1 := by
    apply (logOuterCutoff a b).one_of_mem_closedBall
    change dist u 0 ≤ logRadius a b + 1
    change dist u 0 < logRadius a b + 1 at hmem
    exact le_of_lt hmem
  simp [patchedExp, expCorrection, heta]

theorem logPullbackCLM_eq_actual (a b : ℝ) (ha : 0 < a) (W : SchwartzMap ℝ ℂ)
    (hsupp : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) (u : ℝ) :
    logPullbackCLM a b W u = W (Real.exp u) := by
  rw [logPullbackCLM_apply]
  by_cases hW : W (Real.exp u) = 0
  · by_cases hcut : logCutoff a b u = 0
    · simp [hcut, hW]
    · rw [patchedExp_eq_exp_of_cutoff_ne_zero a b u hcut, hW, smul_zero]
  · have hcut := logCutoff_eq_one_of_source a b ha u (hsupp hW)
    rw [patchedExp_eq_exp_of_cutoff_ne_zero a b u (by rw [hcut]; norm_num), hcut, one_smul]

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

theorem compact_family_deriv_sup_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ u : ℝ, ‖iteratedFDeriv ℝ j (F σ) u‖ ≤ C := by
  have hc := (section_iteratedDeriv_smooth F hF j).continuous.norm
  obtain ⟨M, hM⟩ := (hJ.prod hK).bddAbove_image hc.continuousOn
  refine ⟨|M| + 1, by positivity, ?_⟩
  intro σ hσ u
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hu : u ∈ K
  · exact (hM (Set.mem_image_of_mem _ (show (σ, u) ∈ J ×ˢ K from ⟨hσ, hu⟩))).trans
      (by linarith [le_abs_self M])
  · have hs : Function.support (iteratedDeriv j (F σ)) ⊆ K :=
      (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
        (closure_minimal (hsupp σ) hK.isClosed))
    have hz : iteratedDeriv j (F σ) u = 0 := by by_contra hn; exact hu (hs hn)
    simp only [hz, norm_zero]
    positivity

theorem compact_family_mul_deriv_L1_source_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : SchwartzMap ℝ ℂ, ∀ σ ∈ J,
      (∫ u : ℝ, ‖iteratedDeriv j (fun u => F σ u * W u) u‖) ≤
        C * (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  choose c hc hcb using fun i : Fin (j + 1) => compact_family_deriv_sup_bound F hF K hK hsupp J hJ i.val
  let D := (∑ i : Fin (j + 1), c i) + 1
  have hD : 0 < D := by
    have : 0 ≤ ∑ i : Fin (j + 1), c i := Finset.sum_nonneg (fun i _ => (hc i).le)
    dsimp [D]
    linarith
  have hder (i : ℕ) (hi : i ≤ j) (σ : ℝ) (hσ : σ ∈ J) (u : ℝ) :
      ‖iteratedFDeriv ℝ i (F σ) u‖ ≤ D := by
    let k : Fin (j + 1) := ⟨i, by omega⟩
    have hsum : c k ≤ ∑ l : Fin (j + 1), c l :=
      Finset.single_le_sum (fun l _ => (hc l).le) (Finset.mem_univ k)
    exact (hcb k σ hσ u).trans (by dsimp [D]; linarith)
  let B : ℝ := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * D
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨(B + 1) * (volume.real K + 1), by positivity, ?_⟩
  intro W σ hσ
  let S : ℝ := (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hWder (k : ℕ) (hk : k ≤ j) (u : ℝ) : ‖iteratedFDeriv ℝ k W u‖ ≤ S := by
    have hle : schwartzSeminormFamily ℝ ℝ ℂ (0, k) ≤
        (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
      Finset.le_sup (f := schwartzSeminormFamily ℝ ℝ ℂ) (by simp [hk])
    exact (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ W k u).trans (Seminorm.le_def.mp hle W)
  have hb (u : ℝ) : ‖iteratedDeriv j (fun u => F σ u * W u) u‖ ≤ (B + 1) * S := by
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hfσ : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
    apply (norm_iteratedFDeriv_mul_le hfσ (W.smooth ⊤) u (n := j) (by first | simp | exact_mod_cast le_top)).trans
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * D * S := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hder i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) σ hσ u) (by positivity))
          (hWder (j - i) (Nat.sub_le _ _) u) (norm_nonneg _) (by positivity)
      _ = B * S := by rw [← Finset.sum_mul]
      _ ≤ (B + 1) * S := mul_le_mul_of_nonneg_right (by linarith) hS
  have hmul : Function.support (fun u => F σ u * W u) ⊆ K := by
    intro u hu
    exact hsupp σ (mul_ne_zero_iff.mp hu).1
  have hs : Function.support (iteratedDeriv j (fun u => F σ u * W u)) ⊆ K :=
    (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset _ j).trans
      (closure_minimal hmul hK.isClosed))
  have hzero : ∀ u, u ∉ K → ‖iteratedDeriv j (fun u => F σ u * W u) u‖ = 0 := by
    intro u hu
    have hz : iteratedDeriv j (fun u => F σ u * W u) u = 0 := by by_contra hn; exact hu (hs hn)
    simp [hz]
  have hi := norm_setIntegral_le_of_norm_le_const («μ» := volume)
    (f := fun u => ‖iteratedDeriv j (fun u => F σ u * W u) u‖) hK.measure_lt_top
    (C := (B + 1) * S) (fun u _ => by simpa using hb u)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    Real.norm_of_nonneg (integral_nonneg (fun u => norm_nonneg _))] at hi
  calc
    _ ≤ ((B + 1) * S) * volume.real K := hi
    _ ≤ ((B + 1) * S) * (volume.real K + 1) := by gcongr; linarith
    _ = _ := by dsimp [S]; ring

end CubicReflectionKernel

end

end OAI

end


