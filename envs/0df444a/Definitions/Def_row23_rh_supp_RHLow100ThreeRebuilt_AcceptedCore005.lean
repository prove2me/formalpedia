-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100ThreeRebuilt_AcceptedCore005
-- name    : row23_rh_supp_RHLow100ThreeRebuilt_AcceptedCore005
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T20:11:26.483928+00:00
-- url     : https://prove2.me/theorems/6e69d997-58dd-4db0-8488-528bbfc0ccfd
-- title:
--   Row 23 RH support: RHLow100ThreeRebuilt.AcceptedCore005
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLow100ThreeRebuilt_AcceptedCore004
/-
Compact certificate adaptation of sometik179's height-14–100 proof,
Prove2Me submission c9908072-d99a-4431-aad8-a72c6352619a (2026-10-03).
The theta/Mellin attribution to Gabewhigham is retained in the source.
Large records are reconstructed by ordinary Lean definitions. The original
kernel validators still establish every numerical certificate condition.
-/
import Definitions.Def_row23_rh_supp_RHLow100ThetaReplacement
import Theorems.Thm_TaoFivePrimes_rh14to100_moments_enclosed
import Definitions.Def_row23_rh_supp_RHLow100TranslationReplacement
import Definitions.Def_row23_rh_supp_RHLow100BernsteinReplacement
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic
import Mathlib.Tactic.GCongr

/- Ordinary finite arithmetic definitions extracted from sometik179's
height-14–100 certificate, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a.
Theta/Mellin attribution to Gabewhigham is retained. No certificate assertion
or RH theorem is supplied in this definition interface. -/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false


/- Source module: GlobalTaylorCertificate. -/
section Height100Module18

open Complex Finset Metric
open scoped BigOperators
set_option autoImplicit false
set_option exponentiation.threshold 1024

namespace TaoZetaGlobal

lemma norm_iteratedDeriv_completedZeta (n : ℕ) :
    ‖iteratedDeriv n completedRiemannZeta₀ (1 / 2)‖ ≤ 
      n.factorial * (10^155) / (256 : ℝ) ^ n := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num)
    differentiable_completedZeta₀.diffContOnCl
  intro z hz
  have habs : |z.re - 1 / 2| ≤  (256 : ℝ) := by
    have h := Complex.abs_re_le_norm (z - (1 / 2 : ℂ))
    rw [mem_sphere_iff_norm.mp hz] at h
    simpa using h
  apply TaoZetaWide256.norm_completedRiemannZeta₀_le <;> linarith [(abs_le.mp habs).1, (abs_le.mp habs).2]

noncomputable def taylorTerm (z : ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ)⁻¹ • (z - 1 / 2) ^ n •
    iteratedDeriv n completedRiemannZeta₀ (1 / 2)

lemma norm_taylorTerm_le (z : ℂ) (n : ℕ) :
    ‖taylorTerm z n‖ ≤  (10^155) * (‖z - 1 / 2‖ / 256) ^ n := by
  have h := norm_iteratedDeriv_completedZeta n
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  unfold taylorTerm
  simp only [norm_smul, norm_inv, Complex.norm_natCast, norm_pow]
  calc
    (n.factorial : ℝ)⁻¹ * (‖z - 1 / 2‖ ^ n *
        ‖iteratedDeriv n completedRiemannZeta₀ (1 / 2)‖) ≤ 
      (n.factorial : ℝ)⁻¹ * (‖z - 1 / 2‖ ^ n *
        (n.factorial * (10^155) / (256 : ℝ) ^ n)) := by gcongr
    _ = (10^155) * (‖z - 1 / 2‖ / 256) ^ n := by
      rw [div_pow]
      field_simp

/-- A uniform certified truncation bound, with no assumptions about computed coefficients. -/
lemma norm_taylor_remainder_le (z : ℂ) (hz : ‖z - 1 / 2‖ < 256) (N : ℕ) :
    ‖completedRiemannZeta₀ z - ∑ n ∈ range N, taylorTerm z n‖ ≤ 
      (10^155) * (‖z - 1 / 2‖ / 256) ^ N / (1 - ‖z - 1 / 2‖ / 256) := by
  let q : ℝ := ‖z - 1 / 2‖ / 256
  have hq0 : 0 ≤  q := by positivity
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hs : HasSum (taylorTerm z) (completedRiemannZeta₀ z) :=
    Complex.hasSum_taylorSeries_of_entire differentiable_completedZeta₀ (1 / 2) z
  have htail : completedRiemannZeta₀ z - ∑ n ∈ range N, taylorTerm z n =
      ∑' n : ℕ, taylorTerm z (n + N) := by
    have h := hs.summable.sum_add_tsum_nat_add N
    rw [hs.tsum_eq] at h
    apply sub_eq_iff_eq_add.mpr
    simpa [add_comm] using h.symm
  rw [htail]
  have hgeo : HasSum (fun n : ℕ => ((10^155) * q ^ N) * q ^ n)
      (((10^155) * q ^ N) * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left ((10^155) * q ^ N)
  have hbound := tsum_of_norm_bounded hgeo (fun n : ℕ => by
    calc ‖taylorTerm z (n + N)‖ ≤  (10^155) * q ^ (n + N) := norm_taylorTerm_le z (n + N)
      _ = ((10^155) * q ^ N) * q ^ n := by rw [pow_add]; ring)
  simpa only [q, div_eq_mul_inv] using hbound

lemma norm_taylor_remainder_512 (z : ℂ) (hz : ‖z - 1 / 2‖ ≤  104) :
    ‖completedRiemannZeta₀ z - ∑ n ∈ range 512, taylorTerm z n‖ ≤  1 / 10 ^ 45 := by
  have hr := norm_taylor_remainder_le z (by linarith) 512
  have hq : ‖z - 1 / 2‖ / 256 ≤  (13 / 32 : ℝ) := by linarith
  have hq0 : 0 ≤  ‖z - 1 / 2‖ / 256 := by positivity
  apply hr.trans
  calc
    (10^155) * (‖z - 1 / 2‖ / 256) ^ 512 / (1 - ‖z - 1 / 2‖ / 256) ≤ 
        (10^155) * (13 / 32 : ℝ) ^ 512 / (1 - 13 / 32) := by
      gcongr
    _ ≤  1 / 10 ^ 45 := by norm_num

end TaoZetaGlobal

end Height100Module18

/- Source module: MellinMoments. -/
section Height100Module19

open Complex MeasureTheory Set Filter Asymptotics
open scoped Topology
set_option autoImplicit false

namespace TaoZetaCertificate

noncomputable def logKernel : ℕ → ℝ → ℂ
  | 0 => ZetaSix.P.f_modif
  | n + 1 => fun t => Real.log t • logKernel n t

lemma logKernel_eq (n : ℕ) (t : ℝ) :
    logKernel n t = (Real.log t) ^ n • ZetaSix.P.f_modif t := by
  induction n with
  | zero => simp [logKernel]
  | succ n ih => simp only [logKernel, ih, pow_succ]; rw [smul_smul]; congr 1; ring

lemma logKernel_locallyIntegrable (n : ℕ) :
    LocallyIntegrableOn (logKernel n) (Ioi 0) := by
  induction n with
  | zero => exact ZetaSix.P.hf_modif_int
  | succ n ih =>
    exact MeasureTheory.LocallyIntegrableOn.continuousOn_smul isOpen_Ioi.isLocallyClosed ih
      (fun t ht => (Real.continuousAt_log (ne_of_gt ht)).continuousWithinAt)

lemma logKernel_top (n : ℕ) (r : ℝ) :
    logKernel n =O[atTop] (fun t : ℝ => t ^ r) := by
  induction n generalizing r with
  | zero =>
    exact ZetaSix.P.isStrongFEPair_toStrongFEPair.hf_top r
  | succ n ih =>
    have h := isBigO_rpow_top_log_smul (a := -(r - 1)) (b := -r) (by linarith)
      (by simpa only [neg_neg] using ih (r - 1))
    simpa only [neg_neg, logKernel] using h

lemma logKernel_zero (n : ℕ) (r : ℝ) :
    logKernel n =O[𝓝[>] 0] (fun t : ℝ => t ^ r) := by
  induction n generalizing r with
  | zero =>
    exact ZetaSix.P.isStrongFEPair_toStrongFEPair.hf_zero r
  | succ n ih =>
    have h := isBigO_rpow_zero_log_smul (a := -(r + 1)) (b := -r) (by linarith)
      (by simpa only [neg_neg] using ih (r + 1))
    simpa only [neg_neg, logKernel] using h

lemma logKernel_mellin_hasDerivAt (n : ℕ) (s : ℂ) :
    HasDerivAt (mellin (logKernel n)) (mellin (logKernel (n + 1)) s) s := by
  exact (mellin_hasDerivAt_of_isBigO_rpow (logKernel_locallyIntegrable n)
    (logKernel_top n (-(s.re + 1))) (by linarith)
    (logKernel_zero n (-(s.re - 1))) (by linarith)).2

lemma logKernel_mellin_convergent (n : ℕ) (s : ℂ) :
    MellinConvergent (logKernel n) s := by
  exact mellinConvergent_of_isBigO_rpow (logKernel_locallyIntegrable n)
    (logKernel_top n (-(s.re + 1))) (by linarith)
    (logKernel_zero n (-(s.re - 1))) (by linarith)

lemma iteratedDeriv_mellin_kernel (n : ℕ) :
    iteratedDeriv n (mellin ZetaSix.P.f_modif) = mellin (logKernel n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext fun s => (logKernel_mellin_hasDerivAt n s).deriv

lemma completedZeta_derivative_moment (n : ℕ) (s : ℂ) :
    iteratedDeriv n completedRiemannZeta₀ s =
      mellin (logKernel n) (s / 2) / (2 : ℂ) ^ (n + 1) := by
  have hf : Differentiable ℂ (mellin ZetaSix.P.f_modif) :=
    fun s => (logKernel_mellin_hasDerivAt 0 s).differentiableAt
  have he : completedRiemannZeta₀ =
      (fun s : ℂ => mellin ZetaSix.P.f_modif ((1 / 2 : ℂ) * s) / 2) := by
    ext z
    change mellin ZetaSix.P.f_modif (z / 2) / 2 = _
    congr 2
    ring
  rw [he, iteratedDeriv_div_const]
  rw [iteratedDeriv_comp_const_mul hf.contDiff, iteratedDeriv_mellin_kernel]
  have hs : (1 / 2 : ℂ) * s = s / 2 := by ring
  dsimp only
  rw [hs]
  rw [pow_succ, div_pow, one_pow]
  field_simp

end TaoZetaCertificate

end Height100Module19

/- Source module: FoldedMoments. -/
section Height100Module20

open Complex MeasureTheory Set HurwitzZeta
set_option autoImplicit false

namespace TaoZetaCertificate

noncomputable def momentIntegrand (n : ℕ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ ((1 / 4 : ℂ) - 1) • logKernel (2 * n) t

noncomputable def outerIntegrand (n : ℕ) (t : ℝ) : ℂ :=
  ((t ^ (-3 / 4 : ℝ) * Real.log t ^ (2 * n) * (evenKernel 0 t - 1) : ℝ) : ℂ)

lemma momentIntegrand_outer (n : ℕ) {t : ℝ} (ht : 1 < t) :
    momentIntegrand n t = outerIntegrand n t := by
  have ht0 : 0 ≤  t := by linarith
  unfold momentIntegrand outerIntegrand
  rw [logKernel_eq, ZetaSix.f_modif_of_one_lt ht]
  have he : (1 / 4 : ℂ) - 1 = ((-3 / 4 : ℝ) : ℂ) := by norm_num
  rw [he, ← Complex.ofReal_cpow ht0]
  simp only [Complex.real_smul, smul_eq_mul]
  push_cast
  ring

lemma momentIntegrand_inner (n : ℕ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    momentIntegrand n t =
      ((t ^ (-5 / 4 : ℝ) * Real.log t ^ (2 * n) *
        (evenKernel 0 (1 / t) - 1) : ℝ) : ℂ) := by
  unfold momentIntegrand
  rw [logKernel_eq, ZetaSix.f_modif_of_lt_one ht ht1, ZetaSix.evenKernel_eq_of_pos ht]
  have he : (1 / 4 : ℂ) - 1 = ((-3 / 4 : ℝ) : ℂ) := by norm_num
  rw [he, ← Complex.ofReal_cpow ht.le]
  have hpow : t ^ (-5 / 4 : ℝ) = t ^ (-3 / 4 : ℝ) * t ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_add ht]
    norm_num
  rw [hpow]
  simp only [Complex.real_smul, smul_eq_mul]
  push_cast
  ring

private noncomputable def outerIndicator (n : ℕ) : ℝ → ℂ :=
  (Ioi 1).indicator (outerIntegrand n)

private lemma integral_outerIndicator (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), outerIndicator n t) = ∫ t in Ioi 1, outerIntegrand n t := by
  rw [outerIndicator, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi]
  norm_num

private lemma reciprocal_integrand (n : ℕ) (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
    (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) • outerIndicator n (t ^ (-1 : ℝ)) =
      (Ioo (0 : ℝ) 1).indicator (momentIntegrand n) t := by
  have ht0 : 0 < t := ht
  rw [Real.rpow_neg_one]
  rcases lt_or_ge t 1 with h | h
  · have hinv : 1 < t⁻¹ := by rw [lt_inv_comm₀ (by norm_num) ht0]; simpa using h
    rw [indicator_of_mem (show t ∈ Ioo (0 : ℝ) 1 from ⟨ht0, h⟩),
      outerIndicator, indicator_of_mem (show t⁻¹ ∈ Ioi (1 : ℝ) from hinv), momentIntegrand_inner n ht0 h]
    unfold outerIntegrand
    have hpow : (t⁻¹) ^ (-3 / 4 : ℝ) = t ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_neg_one t, ← Real.rpow_mul ht0.le]
      norm_num
    have hlog : Real.log (t⁻¹) ^ (2 * n) = Real.log t ^ (2 * n) := by
      rw [Real.log_inv, Even.neg_pow (even_two_mul n)]
    rw [hpow, hlog]
    have he : t ^ (-2 : ℝ) * t ^ (3 / 4 : ℝ) = t ^ (-(5 / 4) : ℝ) := by
      rw [← Real.rpow_add ht0]
      norm_num
    norm_num only [abs_neg, abs_one, one_mul]
    rw [Complex.real_smul]
    push_cast
    rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, he]
    simp only [one_div]
  · have hinv : t⁻¹ ≤  1 := by rw [inv_le_one_iff₀]; right; exact h
    rw [indicator_of_notMem (by simp; intro _; exact h), outerIndicator,
      indicator_of_notMem (by simpa using not_lt.mpr hinv)]
    simp

lemma integral_moment_inner (n : ℕ) :
    (∫ t in Ioc (0 : ℝ) 1, momentIntegrand n t) = ∫ t in Ioi 1, outerIntegrand n t := by
  have h := integral_comp_rpow_Ioi (outerIndicator n) (by norm_num : (-1 : ℝ) ≠ 0)
  rw [integral_outerIndicator, setIntegral_congr_fun measurableSet_Ioi (reciprocal_integrand n)] at h
  rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    show Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo (0 : ℝ) 1 by ext t; simp; tauto] at h
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  exact h

lemma mellin_even_moment_folded (n : ℕ) :
    mellin (logKernel (2 * n)) (1 / 4) = 2 * ∫ t in Ioi 1, outerIntegrand n t := by
  have hi : IntegrableOn (momentIntegrand n) (Ioi (0 : ℝ)) :=
    logKernel_mellin_convergent (2 * n) (1 / 4)
  have hi0 := hi.mono_set (Ioc_subset_Ioi_self : Ioc (0 : ℝ) 1 ⊆ Ioi 0)
  have hi1 := hi.mono_set (Ioi_subset_Ioi (show (0 : ℝ) ≤  1 by norm_num))
  change (∫ t in Ioi (0 : ℝ), momentIntegrand n t) = _
  rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
  rw [setIntegral_union (by simp [Set.disjoint_left]) measurableSet_Ioi hi0 hi1,
    integral_moment_inner n,
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => momentIntegrand_outer n ht)]
  ring

lemma even_derivative_moment_folded (n : ℕ) :
    iteratedDeriv (2 * n) completedRiemannZeta₀ (1 / 2) =
      (∫ t in Ioi 1, outerIntegrand n t) / (2 : ℂ) ^ (2 * n) := by
  rw [completedZeta_derivative_moment]
  have hc : (1 / 2 : ℂ) / 2 = 1 / 4 := by norm_num
  rw [hc, mellin_even_moment_folded, pow_succ]
  field_simp

end TaoZetaCertificate

end Height100Module20

/- Source module: Symmetry. -/
section Height100Module21

open Complex MeasureTheory Set
open scoped ComplexConjugate
set_option autoImplicit false

namespace TaoZetaCertificate

lemma conj_kernel {t : ℝ} (ht : 0 < t) :
    conj (ZetaSix.P.f_modif t) = ZetaSix.P.f_modif t := by
  rcases lt_trichotomy t 1 with h | rfl | h
  · rw [ZetaSix.f_modif_of_lt_one ht h]
    simp
  · rw [ZetaSix.f_modif_one]
    simp
  · rw [ZetaSix.f_modif_of_one_lt h]
    simp

lemma completedZeta_conj (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  change mellin ZetaSix.P.f_modif (conj s / 2) / 2 =
    conj (mellin ZetaSix.P.f_modif (s / 2) / 2)
  rw [map_div₀, map_ofNat]
  congr 1
  rw [mellin, mellin, ← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht0 : 0 < t := ht
  have htarg : (t : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht0.le]
    exact ne_of_lt Real.pi_pos
  have he : conj s / 2 - 1 = conj (s / 2 - 1) := by
    simp only [map_sub, map_div₀, map_one, map_ofNat]
  dsimp only
  rw [he, Complex.cpow_conj _ _ htarg]
  simp only [smul_eq_mul, map_mul, conj_ofReal, conj_kernel ht0]

lemma odd_taylor_derivative_zero (n : ℕ) :
    iteratedDeriv (2 * n + 1) completedRiemannZeta₀ (1 / 2) = 0 := by
  have hf : (fun z => completedRiemannZeta₀ (1 - z)) = completedRiemannZeta₀ :=
    funext completedRiemannZeta₀_one_sub
  have h := congrFun (congrArg (iteratedDeriv (2 * n + 1)) hf) (1 / 2)
  rw [iteratedDeriv_comp_const_sub] at h
  norm_num [pow_add, pow_mul] at h
  linear_combination -h / 2

end TaoZetaCertificate

end Height100Module21

/- Source module: ComplexTaylorBounds. -/
section Height100Module22

open Complex Finset Metric Filter
namespace CertifiedComplexTaylor
open CertifiedTaylorQuadrature

noncomputable def polynomial (f : ℂ → ℂ) (c : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ range N, coefficient f c n*(z-c)^n
noncomputable def remainder (f : ℂ → ℂ) (c : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  f z-polynomial f c N z

lemma series_sum (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c z : ℂ) :
    HasSum (fun n : ℕ => coefficient f c n*(z-c)^n) (f z) := by
  have h := Complex.hasSum_taylorSeries_of_entire hf c z
  convert! h using 1
  ext n
  simp only [coefficient,smul_eq_mul]
  ring

lemma remainder_eq_tsum (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c z : ℂ) (N : ℕ) :
    remainder f c N z = ∑' n : ℕ, coefficient f c (n+N)*(z-c)^(n+N) := by
  have hs := series_sum f hf c z
  have h := hs.summable.sum_add_tsum_nat_add N
  rw [hs.tsum_eq] at h
  unfold remainder polynomial
  apply sub_eq_iff_eq_add.mpr
  simpa [add_comm] using h.symm

lemma remainder_bound (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ)
    (R M r : ℝ) (hR : 0< R) (hM : 0≤ M) (hr : 0≤ r) (hrR : r< R)
    (hb : ∀ z ∈ sphere c R, ‖f z‖≤ M) (N : ℕ) (z : ℂ) (hz : ‖z-c‖≤ r) :
    ‖remainder f c N z‖≤ M*(r/R)^N/(1-r/R) := by
  have hq0 : 0≤ r/R := div_nonneg hr hR.le
  have hq1 : r/R<1 := (div_lt_one hR).mpr hrR
  rw [remainder_eq_tsum f hf c z N]
  have hgeo := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (M*(r/R)^N)
  have hterms : ∀ n : ℕ, ‖coefficient f c (n+N)*(z-c)^(n+N)‖ ≤  (M*(r/R)^N)*(r/R)^n := by
    intro n
    rw [norm_mul,norm_pow]
    calc
      _ ≤  (M/R^(n+N))*r^(n+N) := by
        gcongr
        exact coefficient_bound f hf c R M hR hb (n+N)
      _ = _ := by rw [div_pow,div_pow,pow_add,pow_add]; ring
  simpa only [div_eq_mul_inv] using tsum_of_norm_bounded hgeo hterms

lemma coefficient_sub (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (c : ℂ) (n : ℕ) :
    coefficient (fun z => f z-g z) c n = coefficient f c n-coefficient g c n := by
  unfold coefficient
  change iteratedDeriv n (f-g) c/(n.factorial:ℂ)=_
  rw [iteratedDeriv_sub hf.contDiff.contDiffAt hg.contDiff.contDiffAt,sub_div]

/-- Uniform global approximation on one circle transfers to every local Taylor coefficient. -/
lemma coefficient_error (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (c : ℂ) (R δ : ℝ) (hR : 0< R) (hb : ∀ z ∈ sphere c R, ‖f z-g z‖≤ δ) (n : ℕ) :
    ‖coefficient f c n-coefficient g c n‖≤ δ/R^n := by
  rw [← coefficient_sub f g hf hg]
  exact coefficient_bound _ (hf.sub hg) c R δ hR hb n

end CertifiedComplexTaylor

end Height100Module22

/- Source module: WideStrip. -/
section Height100Module23

open Complex MeasureTheory Set HurwitzZeta Real
open scoped Real
set_option autoImplicit false

namespace TaoZetaWide
open ZetaSix

noncomputable def maj (t : ℝ) : ℝ :=
  if t ≤  1 then 21 / 10 * (t ^ (-14 : ℝ) * rexp (-π / t))
  else 21 / 10 * (t ^ (12 : ℝ) * rexp (-π * t))

lemma integrableOn_outer :
    IntegrableOn (fun t : ℝ => t ^ (12 : ℝ) * rexp (-π * t)) (Ioi 1) := by
  simpa only [Real.rpow_ofNat] using
    (ZetaSix.integrableOn_pow_mul_exp 12).mono_set (Ioi_subset_Ioi zero_le_one)

lemma outer_le :
    (∫ t in Ioi (1 : ℝ), t ^ (12 : ℝ) * rexp (-π * t)) ≤  (640 : ℝ) / (21 / 10) := by
  have h := MeasureTheory.setIntegral_mono_set
    (ZetaSix.integrableOn_pow_mul_exp 12)
    (Filter.Eventually.of_forall (fun x : ℝ => by positivity :
      ∀ x : ℝ, 0 ≤  x ^ 12 * rexp (-π * x)))
    (Filter.Eventually.of_forall (Ioi_subset_Ioi (show (0 : ℝ) ≤  1 by norm_num)))
  simp only [Real.rpow_ofNat] at *
  rw [ZetaSix.integral_pow_mul_exp] at h
  have hp : (3 : ℝ) ^ 13 ≤  π ^ 13 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_three.le 13
  have hpi : (0 : ℝ) < π ^ 13 := by positivity
  have hb : (Nat.factorial 12 : ℝ) / π ^ 13 ≤  640 / (21 / 10) := by
    rw [div_le_iff₀ hpi]
    norm_num [Nat.factorial] at *
    nlinarith
  exact h.trans hb

/-- The kernel of the substituted integral: `u^{-1/2} e^{-π u}` cut off below `1`. -/
private noncomputable def gInd : ℝ → ℝ :=
  Set.indicator (Ioi 1) fun u => u ^ (12 : ℝ) * rexp (-π * u)

private lemma gInd_integrableOn : IntegrableOn gInd (Ioi (0 : ℝ)) := by
  rw [gInd]
  exact (integrableOn_outer.integrable_indicator measurableSet_Ioi).integrableOn

private lemma integral_gInd : (∫ y in Ioi (0 : ℝ), gInd y)
    = ∫ u in Ioi (1 : ℝ), u ^ (12 : ℝ) * rexp (-π * u) := by
  rw [gInd, MeasureTheory.integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Set.Ioi_inter_Ioi]
  norm_num

private lemma cov_ptwise (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
    (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • gInd (x ^ (-1 : ℝ))
      = (Ioo (0 : ℝ) 1).indicator (fun x => x ^ (-14 : ℝ) * rexp (-π / x)) x := by
  have hx0 : 0 < x := hx
  have hinv : x ^ (-1 : ℝ) = x⁻¹ := by rw [Real.rpow_neg_one]
  rcases lt_or_ge x 1 with h | h
  · have h1 : (1 : ℝ) < x⁻¹ := by rw [lt_inv_comm₀ (by norm_num) hx0]; simpa using h
    rw [Set.indicator_of_mem (show x ∈ Ioo (0 : ℝ) 1 from ⟨hx0, h⟩), gInd, hinv,
      Set.indicator_of_mem (mem_Ioi.mpr h1)]
    have hd : -π * x⁻¹ = -π / x := by field_simp
    have hpow : (x⁻¹) ^ (12 : ℝ) = x ^ (-12 : ℝ) := by
      rw [← Real.rpow_neg_one x, ← Real.rpow_mul hx0.le]
      norm_num
    rw [hd, hpow, smul_eq_mul]
    have hxx : x ^ ((-1 : ℝ) - 1) * x ^ (-12 : ℝ) = x ^ (-14 : ℝ) := by
      rw [← Real.rpow_add hx0]
      norm_num
    rw [show |(-1 : ℝ)| = 1 by norm_num, one_mul, ← mul_assoc, hxx]
  · have h1 : x⁻¹ ≤  1 := by rw [inv_le_one_iff₀]; right; exact h
    rw [Set.indicator_of_notMem (by simp; intro _; exact h), gInd, hinv,
      Set.indicator_of_notMem (by simp [not_lt.2 h1])]
    simp

lemma integrableOn_inner :
    IntegrableOn (fun x : ℝ => x ^ (-14 : ℝ) * rexp (-π / x)) (Ioc (0 : ℝ) 1) := by
  have h1 : IntegrableOn
      (fun x : ℝ => (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • gInd (x ^ (-1 : ℝ))) (Ioi 0) :=
    (MeasureTheory.integrableOn_Ioi_comp_rpow_iff gInd (by norm_num : (-1 : ℝ) ≠ 0)).mpr
      gInd_integrableOn
  have h2 : IntegrableOn
      ((Ioo (0 : ℝ) 1).indicator fun x => x ^ (-14 : ℝ) * rexp (-π / x)) (Ioi 0) :=
    h1.congr_fun cov_ptwise measurableSet_Ioi
  have h3 := (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).mp h2
  rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ioo,
    show Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo (0 : ℝ) 1 by
      ext x; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]; tauto] at h3
  rw [IntegrableOn, ← MeasureTheory.Measure.restrict_congr_set
    (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  exact h3

lemma integral_inner : (∫ x in Ioc (0 : ℝ) 1, x ^ (-14 : ℝ) * rexp (-π / x))
    = ∫ u in Ioi (1 : ℝ), u ^ (12 : ℝ) * rexp (-π * u) := by
  have hcov := MeasureTheory.integral_comp_rpow_Ioi gInd (by norm_num : (-1 : ℝ) ≠ 0)
  rw [integral_gInd] at hcov
  rw [setIntegral_congr_fun measurableSet_Ioi cov_ptwise] at hcov
  rw [MeasureTheory.integral_indicator measurableSet_Ioo, Measure.restrict_restrict
    measurableSet_Ioo, show Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo (0 : ℝ) 1 by
      ext x; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]; tauto] at hcov
  rw [← MeasureTheory.Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  exact hcov

lemma integrableOn_maj_Ioc : IntegrableOn maj (Ioc (0 : ℝ) 1) := by
  have h : IntegrableOn (fun x : ℝ => 21 / 10 * (x ^ (-14 : ℝ) * rexp (-π / x)))
      (Ioc (0 : ℝ) 1) := integrableOn_inner.const_mul (21 / 10)
  refine h.congr_fun ?_ measurableSet_Ioc
  intro t ht
  simp [maj, ht.2]

lemma integrableOn_maj_Ioi : IntegrableOn maj (Ioi (1 : ℝ)) := by
  have h : IntegrableOn (fun t : ℝ => 21 / 10 * (t ^ (12 : ℝ) * rexp (-π * t)))
      (Ioi (1 : ℝ)) := integrableOn_outer.const_mul (21 / 10)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t ht
  simp [maj, not_le.2 (mem_Ioi.mp ht)]

lemma integrableOn_maj : IntegrableOn maj (Ioi 0) := by
  rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
  exact integrableOn_maj_Ioc.union integrableOn_maj_Ioi

lemma integral_maj_le : ∫ t in Ioi (0 : ℝ), maj t ≤  1280 := by
  have hsplit : ∫ t in Ioi (0 : ℝ), maj t
      = (∫ t in Ioc (0 : ℝ) 1, maj t) + ∫ t in Ioi (1 : ℝ), maj t := by
    rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
    exact setIntegral_union (by simp [Set.disjoint_left]) measurableSet_Ioi
      integrableOn_maj_Ioc integrableOn_maj_Ioi
  have h1 : ∫ t in Ioc (0 : ℝ) 1, maj t
      = 21 / 10 * ∫ u in Ioi (1 : ℝ), u ^ (12 : ℝ) * rexp (-π * u) := by
    rw [setIntegral_congr_fun measurableSet_Ioc
      (g := fun t : ℝ => 21 / 10 * (t ^ (-14 : ℝ) * rexp (-π / t)))
      (fun t ht => by simp [maj, ht.2]), integral_const_mul, integral_inner]
  have h2 : ∫ t in Ioi (1 : ℝ), maj t
      = 21 / 10 * ∫ u in Ioi (1 : ℝ), u ^ (12 : ℝ) * rexp (-π * u) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (g := fun t : ℝ => 21 / 10 * (t ^ (12 : ℝ) * rexp (-π * t)))
      (fun t ht => by simp [maj, not_le.2 (mem_Ioi.mp ht)]), integral_const_mul]
  rw [hsplit, h1, h2]
  have hJ := outer_le
  linarith

lemma norm_integrand_le {s : ℂ} (h0 : -24 ≤  s.re) (h1 : s.re ≤  25) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (s / 2 - 1) • P.f_modif t‖ ≤  maj t := by
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    show (s / 2 - 1).re = s.re / 2 - 1 by simp]
  rcases lt_trichotomy t 1 with hlt | rfl | hgt
  · have hmaj : maj t = 21 / 10 * (t ^ (-14 : ℝ) * rexp (-π / t)) := by simp [maj, hlt.le]
    rw [hmaj]
    have hstep : t ^ (s.re / 2 - 1) * ‖P.f_modif t‖
        ≤  t ^ (s.re / 2 - 1) * (21 / 10 * t ^ (-(1 : ℝ) / 2) * rexp (-π / t)) :=
      mul_le_mul_of_nonneg_left (norm_f_modif_le_of_lt_one ht hlt) (Real.rpow_nonneg ht.le _)
    refine hstep.trans ?_
    have hcomb : t ^ (s.re / 2 - 1) * (21 / 10 * t ^ (-(1 : ℝ) / 2) * rexp (-π / t))
        = 21 / 10 * (t ^ (s.re / 2 - 3 / 2) * rexp (-π / t)) := by
      rw [show s.re / 2 - 3 / 2 = (s.re / 2 - 1) + (-(1 : ℝ) / 2) by ring, Real.rpow_add ht]
      ring
    rw [hcomb]
    have hexp : t ^ (s.re / 2 - 3 / 2) ≤  t ^ (-14 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge ht hlt.le (by linarith)
    have hnn : (0 : ℝ) ≤  rexp (-π / t) := (Real.exp_pos _).le
    nlinarith [Real.rpow_pos_of_pos ht (-14 : ℝ), Real.rpow_pos_of_pos ht (s.re / 2 - 3 / 2)]
  · have hm : maj (1 : ℝ) = 21 / 10 * ((1 : ℝ) ^ (-14 : ℝ) * rexp (-π / 1)) := if_pos le_rfl
    rw [hm, f_modif_one]
    simp only [norm_zero, mul_zero]
    positivity
  · have hmaj : maj t = 21 / 10 * (t ^ (12 : ℝ) * rexp (-π * t)) := by
      simp [maj, not_le.2 hgt]
    rw [hmaj]
    have hstep : t ^ (s.re / 2 - 1) * ‖P.f_modif t‖
        ≤  t ^ (s.re / 2 - 1) * (21 / 10 * rexp (-π * t)) :=
      mul_le_mul_of_nonneg_left (norm_f_modif_le_of_one_lt hgt) (Real.rpow_nonneg ht.le _)
    refine hstep.trans ?_
    have hexp : t ^ (s.re / 2 - 1) ≤  t ^ (12 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hgt.le (by linarith)
    have hnn : (0 : ℝ) ≤  rexp (-π * t) := (Real.exp_pos _).le
    nlinarith [Real.rpow_pos_of_pos ht (12 : ℝ), Real.rpow_pos_of_pos ht (s.re / 2 - 1)]

/-- **Sharpened bound on the entire part of the completed zeta function.**
In the critical strip, `‖Λ₀ s‖ ≤  640`. -/
theorem norm_completedRiemannZeta₀_le {s : ℂ} (h0 : -24 ≤  s.re) (h1 : s.re ≤  25) :
    ‖completedRiemannZeta₀ s‖ ≤  640 := by
  have hdef : completedRiemannZeta₀ s = mellin P.f_modif (s / 2) / 2 := rfl
  rw [hdef, norm_div, Complex.norm_ofNat]
  have hb : ‖mellin P.f_modif (s / 2)‖ ≤  ∫ t in Ioi (0 : ℝ), maj t := by
    rw [mellin]
    refine norm_integral_le_of_norm_le integrableOn_maj ?_
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
    exact norm_integrand_le h0 h1 ht
  have := hb.trans integral_maj_le
  linarith

end TaoZetaWide

end Height100Module23

/- Source module: LocalXiBounds. -/
section Height100Module24

open Complex Metric TaoZetaCertificate
namespace CertifiedLocalXi

noncomputable def xi (s : ℂ) : ℂ :=
  1/2+s*(s-1)/2*completedRiemannZeta₀ s
noncomputable def center (T : ℝ) : ℂ := 1/2+(T:ℂ)*I

lemma xi_entire : Differentiable ℂ xi := by
  unfold xi
  have hΛ := differentiable_completedZeta₀
  fun_prop

lemma center_norm_bound (T : ℝ) (hT : |T|≤ 100) : ‖center T‖≤ 101 := by
  have h := Complex.norm_le_abs_re_add_abs_im (center T)
  norm_num [center] at h
  unfold center
  linarith

lemma center_sub_one_norm_bound (T : ℝ) (hT : |T|≤ 100) : ‖center T-1‖≤ 101 := by
  have h := Complex.norm_le_abs_re_add_abs_im (center T-1)
  norm_num [center] at h
  unfold center
  linarith

lemma xi_circle_bound (T : ℝ) (hT : |T|≤ 100) (z : ℂ) (hz : z ∈ sphere (center T) 24) :
    ‖xi z‖≤ 6000000 := by
  have hzdist : ‖z-center T‖=24 := mem_sphere_iff_norm.mp hz
  have hre : |z.re-1/2|≤ 24 := by
    have h := Complex.abs_re_le_norm (z-center T)
    rw [hzdist] at h
    simpa [center] using h
  have hΛ := TaoZetaWide.norm_completedRiemannZeta₀_le (s:=z)
    (by linarith [(abs_le.mp hre).1]) (by linarith [(abs_le.mp hre).2])
  have hz0 : ‖z‖≤ 125 := by
    have h := norm_add_le (z-center T) (center T)
    rw [sub_add_cancel,hzdist] at h
    linarith [center_norm_bound T hT]
  have hz1 : ‖z-1‖≤ 125 := by
    have h := norm_add_le (z-center T) (center T-1)
    rw [sub_add_sub_cancel,hzdist] at h
    linarith [center_sub_one_norm_bound T hT]
  unfold xi
  calc
    _ ≤  ‖(1/2:ℂ)‖+‖z*(z-1)/2*completedRiemannZeta₀ z‖ := norm_add_le _ _
    _ = 1/2+‖z‖*‖z-1‖/2*‖completedRiemannZeta₀ z‖ := by
      simp only [norm_mul,norm_div]
      norm_num
    _ ≤  1/2+125*125/2*(640:ℝ) := by gcongr
    _ ≤  _ := by norm_num

lemma local_tail_norm (T : ℝ) (hT : |T|≤ 100) (z : ℂ) (hz : ‖z-center T‖≤ 1) :
    ‖CertifiedComplexTaylor.remainder xi (center T) 32 z‖≤ 1/10^36 := by
  have h := CertifiedComplexTaylor.remainder_bound xi xi_entire (center T) 24 6000000 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (xi_circle_bound T hT) 32 z hz
  apply h.trans
  norm_num

end CertifiedLocalXi

end Height100Module24


