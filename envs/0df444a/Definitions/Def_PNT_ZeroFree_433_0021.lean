-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0021
-- name    : PNT_ZeroFree_433_0021
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T12:58:17.459831+00:00
-- url     : https://prove2.me/theorems/9a01f24b-b190-4015-bfcd-a5b8e181825d
-- title:
--   Zero-free region foundations: Poisson.OscillatoryGaussian [0021]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Poisson.OscillatoryGaussian
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Poisson/OscillatoryGaussian.lean#L311-L612

import Definitions.Def_PNT_ZeroFree_433_0021_1

/- Oscillatory Gaussian estimates, split at Lean command boundaries.
Two uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Poisson/OscillatoryGaussian.lean
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

namespace OscSpecial


end OscSpecial

namespace ActualEisensteinCubic

section

open EisensteinEmbedding ConcreteTraceCRT Complex


end

section

open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex


end

open EisensteinEmbedding ConcreteTraceCRT Complex


end ActualEisensteinCubic

namespace GaussianMoment

open scoped Topology
open Filter

noncomputable def realGauss (t : ℝ) (z : ℤ × ℤ) : ℝ :=
  Real.exp (-Real.pi * t * RankTwoPoisson.eisQ z)

theorem realGauss_nonneg (t : ℝ) (z : ℤ × ℤ) :
    0 ≤ realGauss t z := (Real.exp_pos _).le

theorem realGauss_summable {t : ℝ} (ht : 0 < t) :
    Summable (realGauss t) := by
  have h := (RankTwoPoisson.eis_gauss_summable ht).norm
  convert! h using 1
  funext z
  dsimp [realGauss, RankTwoPoisson.eisGauss]
  rw [Complex.norm_exp]
  simp

theorem realGauss_cast (t : ℝ) (z : ℤ × ℤ) :
    (realGauss t z : ℂ) = RankTwoEisShift.shifted t 0 0 z := by
  dsimp [realGauss, RankTwoPoisson.eisQ,
    RankTwoEisShift.shifted, RankTwoEisShift.Q]
  rw [← Complex.ofReal_exp]
  congr 1
  ring_nf

theorem real_gaussian_mass :
    Tendsto (fun t : ℝ => t * (∑' z : ℤ × ℤ, realGauss t z))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 / Real.sqrt 3)) := by
  have hC := EisensteinAbelFiber.shifted_gaussian_mass 0 0
  have hRe := (Complex.continuous_re.tendsto
    (((2 / Real.sqrt 3 : ℝ) : ℂ))).comp hC
  have hsum (t : ℝ) :
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t 0 0 z) =
        (((∑' z : ℤ × ℤ, realGauss t z) : ℝ) : ℂ) := by
    calc
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t 0 0 z) =
          ∑' z : ℤ × ℤ, (realGauss t z : ℂ) := by
            apply tsum_congr
            intro z
            exact (realGauss_cast t z).symm
      _ = (((∑' z : ℤ × ℤ, realGauss t z) : ℝ) : ℂ) :=
        (Complex.ofReal_tsum (realGauss t)).symm
  have hfun (t : ℝ) :
      t * (∑' z : ℤ × ℤ, realGauss t z) =
        (((t : ℂ) * (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t 0 0 z)).re) := by
    rw [hsum]
    norm_cast
  have hEq :
      (fun t : ℝ => t * (∑' z : ℤ × ℤ, realGauss t z)) =
        (Complex.re ∘
          (fun t : ℝ => (t : ℂ) *
            (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t 0 0 z))) := by
    funext t
    exact hfun t
  rw [← hEq] at hRe
  simpa only [Complex.ofReal_re] using hRe

end GaussianMoment

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem dual_gaussian_is_actual_trace_phase
    (a b k l : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) (hη : 0 < η) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let y : O := dualFrequencyEquiv (k,l)
    let q : ℝ := OscSpecial.q (a : ℝ) (b : ℝ)
    let r : ℝ := OscSpecial.r η (a : ℝ) (b : ℝ)
    RankTwoComplex.dualGaussian
        (OscSpecial.A η (a : ℝ) (b : ℝ))
        (OscSpecial.B η (a : ℝ) (b : ℝ))
        (OscSpecial.D η (a : ℝ) (b : ℝ)) (k,l) =
      Complex.exp (-(Real.pi : ℂ) *
        ((η : ℂ) * (q : ℂ) / (4 * (r : ℂ))) *
        (‖eisEmbedding y‖ ^ 2 : ℂ)) *
      ShortDraftTrace.breveE
        (eisEmbedding (-(c * y^2)) / eisLam / ((4*r : ℝ) : ℂ)) := by
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by simpa only [pow_two] using hqZ)
  dsimp only
  rw [OscSpecial.dualGaussian_explicit hη hq (k,l)]
  rw [dualFrequencyEquiv_trace_phase (OscSpecial.r η (a : ℝ) (b : ℝ)) a b k l]
  have hnormC : ((‖eisEmbedding (dualFrequencyEquiv (k,l))‖ : ℂ)^2) =
      (((k^2+k*l+l^2 : ℤ) : ℂ)) := by
    exact_mod_cast dualFrequencyEquiv_norm_sq k l
  rw [hnormC]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem actual_oscillatory_poisson
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) (hη : 0 < η) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let q : ℝ := OscSpecial.q (a : ℝ) (b : ℝ)
    let r : ℝ := OscSpecial.r η (a : ℝ) (b : ℝ)
    (∑' z : O,
      (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ))) =
      (1 / ((OscSpecial.R η (a : ℝ) (b : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
        ∑' y : O,
          Complex.exp (-(Real.pi : ℂ) *
            ((η : ℂ) * (q : ℂ) / (4 * (r : ℂ))) *
            (‖eisEmbedding y‖ ^ 2 : ℂ)) *
          ShortDraftTrace.breveE
            (eisEmbedding (-(c * y^2)) / eisLam / ((4*r : ℝ) : ℂ)) := by
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by simpa only [pow_two] using hqZ)
  dsimp only
  rw [actual_oscillatory_sum_eq_binary a b hc η,
    OscSpecial.oscillatory_gaussian_poisson hη hq]
  congr 1
  let W : O → ℂ := fun y =>
    Complex.exp (-(Real.pi : ℂ) *
      ((η : ℂ) * (OscSpecial.q (a : ℝ) (b : ℝ) : ℂ) /
        (4 * (OscSpecial.r η (a : ℝ) (b : ℝ) : ℂ))) *
      (‖eisEmbedding y‖ ^ 2 : ℂ)) *
    ShortDraftTrace.breveE
      (eisEmbedding (-(ActualEisensteinCoordinates.eval a b * y^2)) /
        eisLam /
        ((4 * OscSpecial.r η (a : ℝ) (b : ℝ) : ℝ) : ℂ))
  calc
    (∑' p : ℤ × ℤ,
      RankTwoComplex.dualGaussian
        (OscSpecial.A η (a : ℝ) (b : ℝ))
        (OscSpecial.B η (a : ℝ) (b : ℝ))
        (OscSpecial.D η (a : ℝ) (b : ℝ)) p) =
        ∑' p : ℤ × ℤ, W (dualFrequencyEquiv p) := by
      apply tsum_congr
      intro p
      simpa only [W] using
        dual_gaussian_is_actual_trace_phase a b p.1 p.2 hc η hη
    _ = ∑' y : O, W y := dualFrequencyEquiv.tsum_eq W

end ActualEisensteinCubic

namespace OscSpecial

private theorem R_eq_four_r_div_q {η a b : ℝ} (hq : q a b ≠ 0) :
    R η a b = 4 * r η a b / q a b := by
  unfold R r
  field_simp [hq]
  ring

private theorem sqrt_R_eq {η a b : ℝ} (_hη : 0 < η) (hq : 0 < q a b) :
    Real.sqrt (R η a b) = 2 * Real.sqrt (r η a b) / Real.sqrt (q a b) := by
  rw [R_eq_four_r_div_q hq.ne']
  rw [Real.sqrt_div' (4 * r η a b) hq.le]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  have hs4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hs4]

theorem prefactor_eq_real_sqrt {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    (1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ))) =
      ((Real.sqrt (q a b) / (2 * Real.sqrt (r η a b)) : ℝ) : ℂ) := by
  have hR : 0 ≤ R η a b := by unfold R; positivity
  have hqS : Real.sqrt (q a b) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hrS : Real.sqrt (r η a b) ≠ 0 :=
    (Real.sqrt_pos.mpr (r_pos hη hq)).ne'
  have hcpow : (R η a b : ℂ) ^ (1 / 2 : ℂ) =
      ((R η a b) ^ (1 / 2 : ℝ) : ℝ) := by
    simpa using (Complex.ofReal_cpow hR (1 / 2 : ℝ)).symm
  rw [hcpow]
  simp only [Complex.ofReal_div]
  rw [← Real.sqrt_eq_rpow, sqrt_R_eq hη hq]
  push_cast
  field_simp [hqS, hrS]

open scoped Topology
open Filter

theorem prefactor_tendsto {a b : ℝ} (hq : 0 < q a b) :
    Tendsto (fun η : ℝ => 1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((Real.sqrt (q a b) / 2 : ℝ) : ℂ))) := by
  have hrcont : Continuous (fun η : ℝ => r η a b) := by
    unfold r
    fun_prop
  have hr : Tendsto (fun η : ℝ => r η a b) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa [r] using (hrcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun η : ℝ => Real.sqrt (r η a b))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_one] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hr
  have hd : Tendsto (fun η : ℝ => Real.sqrt (q a b) /
      (2 * Real.sqrt (r η a b))) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.sqrt (q a b) / 2)) := by
    convert! tendsto_const_nhds.div (tendsto_const_nhds.mul hs)
      (by norm_num : (2 : ℝ) * 1 ≠ 0) using 1 ; simp
  have hc : Tendsto (fun η : ℝ =>
      ((Real.sqrt (q a b) / (2 * Real.sqrt (r η a b)) : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (((Real.sqrt (q a b) / 2 : ℝ) : ℂ))) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hd
  have heq : (fun η : ℝ => 1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ))) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun η : ℝ => ((Real.sqrt (q a b) / (2 * Real.sqrt (r η a b)) : ℝ) : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact prefactor_eq_real_sqrt hη hq
  exact hc.congr' heq.symm

end OscSpecial

namespace GaussianMoment

open scoped Topology
open Filter

private theorem eisQ_nonneg (z : ℤ × ℤ) : 0 ≤ RankTwoPoisson.eisQ z := by
  have h := RankTwoPoisson.eisQ_lower z
  nlinarith [sq_nonneg (z.1 : ℝ), sq_nonneg (z.2 : ℝ)]

private theorem moment_term_bound {t : ℝ} (ht : 0 < t) (z : ℤ × ℤ) :
    RankTwoPoisson.eisQ z * realGauss t z ≤
      (2 / (Real.pi * t)) * realGauss (t / 2) z := by
  have h := gaussian_moment_term_bound (RankTwoPoisson.eisQ z) (Real.pi * t)
    (eisQ_nonneg z) (mul_pos Real.pi_pos ht)
  convert! h using 1 <;> dsimp [realGauss] <;> ring_nf

private theorem moment_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun z : ℤ × ℤ => RankTwoPoisson.eisQ z * realGauss t z) := by
  have hmajor : Summable (fun z : ℤ × ℤ =>
      (2 / (Real.pi * t)) * realGauss (t / 2) z) :=
    (realGauss_summable (t := t / 2) (half_pos ht)).mul_left _
  exact hmajor.of_nonneg_of_le
    (fun z => mul_nonneg (eisQ_nonneg z) (realGauss_nonneg t z))
    (moment_term_bound ht)

private theorem moment_tsum_bound {t : ℝ} (ht : 0 < t) :
    (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss t z) ≤
      (2 / (Real.pi * t)) *
        (∑' z : ℤ × ℤ, realGauss (t / 2) z) := by
  have hmajor : Summable (fun z : ℤ × ℤ =>
      (2 / (Real.pi * t)) * realGauss (t / 2) z) :=
    (realGauss_summable (t := t / 2) (half_pos ht)).mul_left _
  have h := Summable.tsum_le_tsum (moment_term_bound ht)
    (moment_summable ht) hmajor
  simpa only [tsum_mul_left] using h

private theorem moment_tsum_nonneg (t : ℝ) :
    0 ≤ (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss t z) := by
  exact tsum_nonneg fun z => mul_nonneg (eisQ_nonneg z) (realGauss_nonneg t z)

private theorem half_tendsto_within :
    Tendsto (fun t : ℝ => t / 2) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt (fun t : ℝ => t / 2) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    exact half_pos ht

private theorem t_tendsto_zero :
    Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
  tendsto_id.mono_left nhdsWithin_le_nhds

private theorem scaled_half_mass_tendsto :
    Tendsto
      (fun t : ℝ => (t / 2) *
        (∑' z : ℤ × ℤ, realGauss (t / 2) z))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 / Real.sqrt 3)) := by
  simpa only [Function.comp_def] using real_gaussian_mass.comp half_tendsto_within

theorem scaled_moment_vanishes :
    Tendsto
      (fun t : ℝ => t ^ 3 *
        (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss t z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hright : Tendsto
      (fun t : ℝ => (4 / Real.pi) * t *
        ((t / 2) * (∑' z : ℤ × ℤ, realGauss (t / 2) z)))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := (t_tendsto_zero.mul scaled_half_mass_tendsto).const_mul (4 / Real.pi)
    simpa only [zero_mul, mul_zero, Function.comp_def, mul_assoc] using h
  have hleft : Tendsto (fun _ : ℝ => (0 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hleft hright
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    exact mul_nonneg (pow_nonneg ht.le _) (moment_tsum_nonneg t)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    have h := moment_tsum_bound ht
    have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht.le _
    have hmul := mul_le_mul_of_nonneg_left h ht3
    calc
      t ^ 3 * (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss t z) ≤
          t ^ 3 * ((2 / (Real.pi * t)) *
            (∑' z : ℤ × ℤ, realGauss (t / 2) z)) := hmul
      _ = (4 / Real.pi) * t *
          ((t / 2) * (∑' z : ℤ × ℤ, realGauss (t / 2) z)) := by
        field_simp [ht.ne']
        ring

end GaussianMoment

end

end OAI

end


