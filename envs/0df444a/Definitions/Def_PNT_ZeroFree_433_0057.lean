-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0057
-- name    : PNT_ZeroFree_433_0057
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T16:01:27.720569+00:00
-- url     : https://prove2.me/theorems/3aae7f78-4a7e-4d80-9037-683cd660277b
-- title:
--   Zero-free region foundations: QuadraticSieve.MainTermDifference [0057]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.MainTermDifference
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/MainTermDifference.lean#L358-L649

import Definitions.Def_PNT_ZeroFree_433_0057_1

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

open ActualEisensteinCubic QuadraticDivisorCancellation QuadraticMainBoundary


end QuadraticMainTermDifference

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter
namespace CubicReflectionKernel


end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel


theorem gammaMultiplier_strip_bound (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖gammaMultiplier ((σ : ℂ) + t * Complex.I)‖ ≤
        C * (1 + |t|) ^ (4 * A + 4) := by
  obtain ⟨C₁, hC₁, h1⟩ := Gamma_pair_strip_bound (7 / 6) (by norm_num) A
  obtain ⟨C₂, hC₂, h2⟩ := Gamma_pair_strip_bound (5 / 6) (by norm_num) A
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  intro σ hσ t
  have heq : gammaMultiplier ((σ : ℂ) + t * Complex.I) =
      (Complex.Gamma (((7 / 6 : ℝ) : ℂ) + (σ + t * Complex.I)) /
       Complex.Gamma (((7 / 6 : ℝ) : ℂ) - (σ + t * Complex.I))) *
      (Complex.Gamma (((5 / 6 : ℝ) : ℂ) + (σ + t * Complex.I)) /
       Complex.Gamma (((5 / 6 : ℝ) : ℂ) - (σ + t * Complex.I))) := by
    simp only [gammaMultiplier, Complex.ofReal_div, Complex.ofReal_ofNat]
    exact div_mul_div_comm _ _ _ _ |>.symm
  rw [heq, norm_mul]
  calc
    _ ≤ (C₁ * (1 + |t|) ^ (2 * A + 2)) * (C₂ * (1 + |t|) ^ (2 * A + 2)) :=
      mul_le_mul (h1 σ hσ t) (h2 σ hσ t) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [mul_mul_mul_comm, ← pow_add]
      congr 2
      omega

theorem section_deriv_smooth (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (F p.1) p.2) := by
  have hFp : ContDiff ℝ ∞
      (Function.uncurry (fun p : ℝ × ℝ => F p.1)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hFp.fderiv contDiff_snd (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  simpa only [deriv] using hd.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem section_iteratedDeriv_smooth (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv j (F p.1) p.2) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hF
  | succ j ih =>
    simpa only [iteratedDeriv_succ] using
      section_deriv_smooth (fun σ => iteratedDeriv j (F σ)) ih

theorem tsupport_iteratedDeriv_subset (f : ℝ → ℂ) (j : ℕ) :
    tsupport (iteratedDeriv j f) ⊆ tsupport f := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem compact_family_deriv_integrable (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (σ : ℝ) (j : ℕ) :
    Integrable (iteratedDeriv j (F σ)) := by
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (iteratedDeriv j (F σ)) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    exact (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  exact (hs.continuous_iteratedDeriv j (by first | simp | exact_mod_cast le_top)).integrable_of_hasCompactSupport hc

theorem compact_family_deriv_L1_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, (∫ u : ℝ, ‖iteratedDeriv j (F σ) u‖) ≤ C := by
  have hc := (section_iteratedDeriv_smooth F hF j).continuous.norm
  obtain ⟨M, hM⟩ := (hJ.prod hK).bddAbove_image hc.continuousOn
  let C : ℝ := (|M| + 1) * (volume.real K + 1)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro σ hσ
  have hbound : ∀ u ∈ K, ‖iteratedDeriv j (F σ) u‖ ≤ |M| + 1 := by
    intro u hu
    exact (hM (Set.mem_image_of_mem _ (show (σ, u) ∈ J ×ˢ K from ⟨hσ, hu⟩))).trans (by linarith [le_abs_self M])
  have hs : Function.support (iteratedDeriv j (F σ)) ⊆ K :=
    (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  have hzero : ∀ u, u ∉ K → ‖iteratedDeriv j (F σ) u‖ = 0 := by
    intro u hu
    have hz : iteratedDeriv j (F σ) u = 0 := by
      by_contra hn
      exact hu (hs hn)
    simp [hz]
  have hi := norm_setIntegral_le_of_norm_le_const («μ» := volume) (f := fun u => ‖iteratedDeriv j (F σ) u‖)
    hK.measure_lt_top (C := |M| + 1) (fun u hu => by simpa using hbound u hu)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero] at hi
  rw [Real.norm_of_nonneg (integral_nonneg (fun u => norm_nonneg _))] at hi
  exact hi.trans (by dsimp [C]; nlinarith [abs_nonneg M])

theorem compact_family_fourier_power_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      |w| ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_family_deriv_L1_bound F hF K hK hsupp J hJ j
  refine ⟨C / (2 * Real.pi) ^ j, by positivity, ?_⟩
  intro σ hσ w
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hfour := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hs
    (fun k _ => compact_family_deriv_integrable F hF K hK hsupp σ k)
    (by simp : (j : ℕ∞) ≤ ⊤)
  have hid : (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) =
      ‖𝓕 (iteratedDeriv j (F σ)) w‖ := by
    rw [hfour]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  have hn : ‖𝓕 (iteratedDeriv j (F σ)) w‖ ≤ C := by
    apply (VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (iteratedDeriv j (F σ)) w).trans
    exact hb σ hσ
  apply (le_div_iff₀ (by positivity : 0 < (2 * Real.pi) ^ j)).mpr
  rw [← hid] at hn
  calc
    _ = (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := mul_comm _ _
    _ ≤ C := hn

theorem compact_family_fourier_weighted_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      (1 + |w|) ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C₀, hC₀, h0⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ 0
  obtain ⟨Cj, hCj, hj⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ j
  refine ⟨2 ^ j * (C₀ + Cj), by positivity, ?_⟩
  intro σ hσ w
  have hbase : ‖𝓕 (F σ) w‖ ≤ C₀ := by simpa using h0 σ hσ w
  by_cases hw : |w| ≤ 1
  · calc
      _ ≤ 2 ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ ≤ 2 ^ j * C₀ := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hw' : 1 ≤ |w| := le_of_lt (lt_of_not_ge hw)
    calc
      _ ≤ (2 * |w|) ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ = 2 ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := by rw [mul_pow, mul_assoc]
      _ ≤ 2 ^ j * Cj := mul_le_mul_of_nonneg_left (hj σ hσ w) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

def mellinLogFamily (V : ℝ → ℂ) (σ u : ℝ) : ℂ :=
  Real.exp (-σ * u) • V (Real.exp (-u))

theorem mellinLogFamily_smooth (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (Function.uncurry (mellinLogFamily V)) := by
  change ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.exp (-p.1 * p.2) • V (Real.exp (-p.2)))
  exact (Real.contDiff_exp.comp (contDiff_fst.neg.mul contDiff_snd)).smul
    (hV.comp (Real.contDiff_exp.comp contDiff_snd.neg))

theorem mellinLogFamily_support (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (σ : ℝ) :
    Function.support (mellinLogFamily V σ) ⊆ Set.Icc (-Real.log b) (-Real.log a) := by
  intro u hu
  have hv : V (Real.exp (-u)) ≠ 0 := by
    intro hv
    exact hu (by simp [mellinLogFamily, hv])
  have hm := hsupp hv
  have hlow := Real.log_le_log ha hm.1
  have hhigh := Real.log_le_log (Real.exp_pos (-u)) hm.2
  simp only [Real.log_exp] at hlow hhigh
  constructor <;> linarith

theorem mellin_eq_logFamily_fourier (V : ℝ → ℂ) (σ t : ℝ) :
    mellin V ((σ : ℂ) + t * Complex.I) = 𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, mul_zero,  sub_zero, add_zero, Complex.add_im,
    Complex.mul_im, Complex.I_im, mul_one, zero_add]
  rfl

theorem compact_source_mellin_strip_decay (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (lo hi : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc lo hi, ∀ t : ℝ,
      (1 + |t|) ^ j * ‖mellin V ((σ : ℂ) + t * Complex.I)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_family_fourier_weighted_bound
    (mellinLogFamily V) (mellinLogFamily_smooth V hV)
    (Set.Icc (-Real.log b) (-Real.log a)) isCompact_Icc
    (mellinLogFamily_support V a b ha hsupp) (Set.Icc lo hi) isCompact_Icc j
  refine ⟨(1 + 2 * Real.pi) ^ j * C, by positivity, ?_⟩
  intro σ hσ t
  rw [mellin_eq_logFamily_fourier]
  have ht : |t| = (2 * Real.pi) * |t / (2 * Real.pi)| := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    field_simp
  have hbase : 1 + |t| ≤ (1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos, abs_nonneg (t / (2 * Real.pi))]
  calc
    _ ≤ ((1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|)) ^ j *
        ‖𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase j) (norm_nonneg _)
    _ = (1 + 2 * Real.pi) ^ j * ((1 + |t / (2 * Real.pi)|) ^ j *
        ‖𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi))‖) := by rw [mul_pow, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb σ hσ _) (by positivity)

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

def mellinData (V : ℝ → ℂ) (s : ℂ) : ℂ := mellin V (-s) * gammaMultiplier s

def mellinEulerData (V : ℝ → ℂ) (j : ℕ) (s : ℂ) : ℂ := (-s) ^ j * mellinData V s

theorem mellinData_strip_decay (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      (1 + |t|) ^ j * ‖mellinData V ((σ : ℂ) + t * Complex.I)‖ ≤ C := by
  let g : ℕ := 4 * A + 4
  obtain ⟨Cγ, hCγ, hγ⟩ := gammaMultiplier_strip_bound A
  obtain ⟨CV, hCV, hVb⟩ := compact_source_mellin_strip_decay V a b ha hsupp hV
    (-(A : ℝ)) (1 / 4) (g + j)
  refine ⟨Cγ * CV, mul_pos hCγ hCV, ?_⟩
  intro σ hσ t
  have hσ' : -σ ∈ Set.Icc (-(A : ℝ)) (1 / 4) := by constructor <;> linarith [hσ.1, hσ.2]
  have hmb := hVb (-σ) hσ' (-t)
  have heq : (-σ : ℝ) + (-t : ℝ) * Complex.I = -((σ : ℂ) + t * Complex.I) := by
    push_cast
    ring
  rw [heq, abs_neg] at hmb
  have hgb : ‖gammaMultiplier ((σ : ℂ) + t * Complex.I)‖ ≤ Cγ * (1 + |t|) ^ g := hγ σ hσ t
  rw [mellinData, norm_mul]
  calc
    _ = ((1 + |t|) ^ j * ‖mellin V (-((σ : ℂ) + t * Complex.I))‖) *
        ‖gammaMultiplier ((σ : ℂ) + t * Complex.I)‖ := by ring
    _ ≤ ((1 + |t|) ^ j * ‖mellin V (-((σ : ℂ) + t * Complex.I))‖) *
        (Cγ * (1 + |t|) ^ g) := mul_le_mul_of_nonneg_left hgb (by positivity)
    _ = Cγ * ((1 + |t|) ^ (g + j) * ‖mellin V (-((σ : ℂ) + t * Complex.I))‖) := by
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmb hCγ.le

theorem weighted_two_to_cauchy {C B : ℝ} (hB : 0 ≤ B) (t : ℝ)
    (h : (1 + |t|) ^ 2 * B ≤ C) : B ≤ C / (1 + t ^ 2) := by
  apply (le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).mpr
  have hpow : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
  exact (mul_le_mul_of_nonneg_left hpow hB).trans (by simpa only [mul_comm] using h)

theorem mellinEulerData_strip_bound (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖mellinEulerData V j ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨C, hC, hb⟩ := mellinData_strip_decay V a b ha hsupp hV A (j + 2)
  refine ⟨((A : ℝ) + 2) ^ j * C, by positivity, ?_⟩
  intro σ hσ t
  apply weighted_two_to_cauchy (norm_nonneg _) t
  have hσabs : |σ| ≤ (A : ℝ) + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hσ.1, hσ.2, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  have hz : ‖(σ : ℂ) + t * Complex.I‖ ≤ ((A : ℝ) + 2) * (1 + |t|) := by
    have hnorm := norm_add_le (σ : ℂ) ((t : ℂ) * Complex.I)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] at hnorm
    nlinarith [abs_nonneg t, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  rw [mellinEulerData, norm_mul, norm_pow, norm_neg]
  calc
    _ ≤ (1 + |t|) ^ 2 * ((((A : ℝ) + 2) * (1 + |t|)) ^ j *
        ‖mellinData V ((σ : ℂ) + t * Complex.I)‖) := by
      gcongr
    _ = ((A : ℝ) + 2) ^ j * ((1 + |t|) ^ (j + 2) *
        ‖mellinData V ((σ : ℂ) + t * Complex.I)‖) := by rw [mul_pow, pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb σ hσ t) (by positivity)

theorem mellinEulerData_differentiableAt (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (j : ℕ) (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (mellinEulerData V j) s :=
  (differentiableAt_id.neg.pow j).mul
    (kernelMellinIntegrand_differentiableAt V a b ha hsupp hV s hs)

theorem mellinEulerData_vertical_integrable (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)) :
    Integrable (fun t : ℝ => mellinEulerData V j ((σ : ℂ) + t * Complex.I)) := by
  obtain ⟨C, hC, hb⟩ := mellinEulerData_strip_bound V a b ha hsupp hV A j
  have hc : Continuous (fun t : ℝ => mellinEulerData V j ((σ : ℂ) + t * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (mellinEulerData_differentiableAt V a b ha hsupp hV j _ ?_).continuousAt.comp
    · fun_prop
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
      linarith [hσ.1]
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by simpa only [div_eq_mul_inv] using hb σ hσ t)

end CubicReflectionKernel

end

end OAI

end


