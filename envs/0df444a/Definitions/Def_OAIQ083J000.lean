-- Prove2me | Definitions.Def_OAIQ083J000
-- name    : OAIQ083J000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T20:17:38.518204+00:00
-- url     : https://prove2.me/theorems/dc9fb9f4-1de7-481e-9ca9-9117de56cc3b
-- title:
--   Definitions bundle OAIQ083J000 of the split of OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 458 declarations of OpenAI's Lean: 61 definitions, 2 inductive types or structures, 2 instances and 393 theorems. The definitions and types are `B1`, `CS`, `Erdos970.Bf`, `Erdos970.CS`, `Erdos970.Cf`, `Erdos970.ChebyshevPsi`, `Erdos970.DeltaSpike`, `Erdos970.Err`, `Erdos970.HIntegral`, `Erdos970.H_auxiliary`, `Erdos970.HolomorphicOn`, `Erdos970.I`, `Erdos970.If_ext`, `Erdos970.If_taxicab`, `Erdos970.I₁`, `Erdos970.I₂`, `Erdos970.I₃`, `Erdos970.I₃₇`, `Erdos970.I₄`, `Erdos970.I₅`, `Erdos970.I₆`, `Erdos970.I₇`, `Erdos970.I₈`, `Erdos970.I₉`, `Erdos970.Lf`, `Erdos970.LogDerivZetaHasBound`, `Erdos970.LogDerivZetaIsHoloSmall`, `Erdos970.MellinConvolution`, `Erdos970.MellinInverseTransform`, `Erdos970.MellinTransform`, `Erdos970.Mertens.E₁`, `Erdos970.Mertens.E₁p`, `Erdos970.Mertens.E₁Λ`, `Erdos970.Mertens.E₂p`, `Erdos970.Mertens.E₂Λ`, `Erdos970.Mertens.E₃`, `Erdos970.Mertens.M`, `Erdos970.Mertens.M_eq_f`, `Erdos970.Mertens.M_eq_summand`, `Erdos970.Mertens.γ` and 23 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `Erdos970_MellinCalculus`, `Erdos970_MertensClassical`, `Erdos970_PNT1_ComplexAnalysis`, `Erdos970_PNT2_LogDerivative`, `Erdos970_PNT3_RiemannZeta`, `Erdos970_PNT4_ZeroFreeRegion`, `Erdos970_PNT5_Strong`, `Erdos970_Rectangle`, `Erdos970_ResidueCalcOnRectangles`, `Erdos970_Sobolev`, `Erdos970_Z0`, `Erdos970_ZetaBounds`, `EulerMaclaurin`, `Jacobsthal_Sieve_SieveScale`, `Mathlib_Analysis_Asymptotics_Asymptotics`, `Mathlib_Analysis_Asymptotics_Uniformly`, `Rectangle`, `Sobolev`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ083J003`; the statements `Erdos970_I1Bound`, `Erdos970.I1Bound_jd`, `Erdos970_I9Bound`, `Erdos970.I9Bound_jd`, `Erdos970_LogDerivZetaBoundedAndHolo`, `Erdos970.LogDerivZetaBoundedAndHolo_jd`, `Erdos970_SmoothedChebyshevClose`, `Erdos970.SmoothedChebyshevClose_jd`, `Erdos970_SmoothedChebyshevPull1` and `Erdos970.SmoothedChebyshevPull1_jd`; the proofs of `Erdos970_I1Bound`, `Erdos970.I1Bound_jd`, `Erdos970_I9Bound`, `Erdos970.I9Bound_jd`, `Erdos970_SmoothedChebyshevClose`, `Erdos970.SmoothedChebyshevClose_jd`, `Erdos970_SmoothedChebyshevPull1`, `Erdos970.SmoothedChebyshevPull1_jd`, `OAI_Erdos970_ErdosPrimeInputs_PrimeErrorDecay_uniform_prime_interval_error`, `OAI.Erdos970.ErdosPrimeInputs.PrimeErrorDecay.uniform_prime_interval_error_jd`, `OAI_JointDickman_characterDistanceDivergence`, `OAI.JointDickman.characterDistanceDivergence_jd`, `OAI_JointDickman_character_agreement_distance_polynomial`, `OAI.JointDickman.character_agreement_distance_polynomial_jd`, `OAI_JointDickman_finiteBinDistributionInput`, `OAI.JointDickman.finiteBinDistributionInput_jd`, `OAI_JointDickman_mellin_prime_sampling_arithmetic`, `OAI.JointDickman.mellin_prime_sampling_arithmetic_jd`, `OAI_JointDickman_primeProductMertensInput`, `OAI.JointDickman.primeProductMertensInput_jd`, `OAI_JointDickman_prime_agreement_distance_polynomial` and `OAI.JointDickman.prime_agreement_distance_polynomial_jd`.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Batteries.Tactic.Lemma

section
-- module Solutions.OAIQ083_JD.Erdos970_MellinCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970

open scoped ContDiff


open _root_.Complex _root_.Topology _root_.Filter _root_.Real _root_.MeasureTheory
  _root_.Set _root_.Function

variable {𝕂 : Type*} [RCLike 𝕂]

@[simp]
lemma Function.support_abs {α : Type*} (f : α → 𝕂) :
    (fun x ↦ ‖f x‖).support = f.support := by
  simp only [support, ne_eq]; simp_rw [norm_ne_zero_iff]

@[simp]
lemma Function.support_ofReal {f : ℝ → ℝ} :
    (fun x ↦ ((f x) : ℂ)).support = f.support := by
  apply Function.support_comp_eq (g := ofReal); simp

noncomputable def MellinConvolution (f g : ℝ → 𝕂) (x : ℝ) : 𝕂 :=
  ∫ y in Ioi 0, f y * g (x / y) / y

noncomputable def DeltaSpike (ν : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  fun x ↦ ν (x ^ (1 / ε)) / ε

@[fun_prop]
lemma DeltaSpikeContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (diffν : ContDiff ℝ 1 ν) : Continuous (fun x ↦ DeltaSpike ν ε x) := by
  apply diffν.continuous.comp (g := ν) _ |>.div_const
  exact continuous_id.rpow_const fun _ ↦ Or.inr <| div_nonneg (by norm_num) εpos.le

noncomputable def Smooth1 (ν : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  MellinConvolution (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) (DeltaSpike ν ε)

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.Erdos970_MertensClassical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970

namespace Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open _root_.ArithmeticFunction hiding log

noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

noncomputable abbrev E₁p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x

noncomputable abbrev E₁ : ℝ := ∑' p : ℕ, if p.Prime then (log p) / (p*(p-1)) else 0

noncomputable abbrev γ : ℝ := (∫ t in Set.Ioi 2, E₁Λ t / (t * log t^2)) + 1 - log (log 2)

noncomputable abbrev E₂Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ

attribute [fun_prop] measurable_from_top

noncomputable def M : ℝ := (∫ t in Set.Ioi 2, E₁p t / (t * log t^2)) + 1 - log (log 2)

noncomputable abbrev E₂p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p - log (log x) - M

noncomputable abbrev M_eq_f (n : ℕ) :=
    if ¬n.Prime then Λ n /(n * log n) else 0

noncomputable def E₃ (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, log (1 - (1:ℝ) / p) + log (log x) + eulerMascheroniConstant

noncomputable abbrev M_eq_summand (p : ℕ) := if p.Prime then log (1 - 1 / p) + 1 / p else 0

end Mertens

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.Erdos970_PNT1_ComplexAnalysis
attribute [-simp] _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970


lemma lem_exprule (n : ℕ) (hn : n ≥ 1) (α β : ℂ) : (n : ℂ) ^ (α + β) = (n : ℂ) ^ α * (n : ℂ) ^ β := by
  apply Complex.cpow_add
                              
  rw [Nat.cast_ne_zero]
                        
  rw [← Nat.one_le_iff_ne_zero]
  exact hn

lemma lem_realbw (b : ℝ) (w : ℂ) : (b * w).re = b * w.re := by
  exact Complex.re_ofReal_mul b w

lemma lem_Euler (a : ℝ) : Complex.exp (a * Complex.I) = Real.cos a + Real.sin a * Complex.I := by
  rw [Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma lem_Reecos (a : ℝ) : (Complex.exp (a * Complex.I)).re = Real.cos a := by
  rw [lem_Euler]
  rw [Complex.add_re]
  rw [Complex.ofReal_re]
  rw [Complex.re_ofReal_mul]
  rw [Complex.I_re]
  simp

lemma lem_coseven (a : ℝ) : Real.cos (-a) = Real.cos a := by
  exact Real.cos_neg a

lemma lem_coseveny (n : ℕ) (_hn : n ≥ 1) (y : ℝ) : Real.cos (-y * Real.log (n : ℝ)) = Real.cos (y * Real.log (n : ℝ)) := by
  rw [neg_mul]
  exact lem_coseven (y * Real.log (n : ℝ))

lemma lem_niyelog (n : ℕ) (hn : n ≥ 1) (y : ℝ) : (n : ℂ) ^ (-y * Complex.I) = Complex.exp (-y * Complex.I * Real.log (n : ℝ)) := by
                                
  have h1 : (n : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    rw [← Nat.one_le_iff_ne_zero]
    exact hn
                                                     
  rw [Complex.cpow_def_of_ne_zero h1]

  rw [← Complex.natCast_log]

  ring_nf

lemma lem_eacosalog (n : ℕ) (_hn : n ≥ 1) (y : ℝ) : (Complex.exp (-y * Complex.I * Real.log (n : ℝ))).re = Real.cos (-y * Real.log (n : ℝ)) := by
                                  
  let a := -y * Real.log (n : ℝ)
                                               
  have h : -y * Complex.I * Real.log (n : ℝ) = a * Complex.I := by
    simp [a, mul_assoc, mul_comm Complex.I]
  rw [h]
                     
  exact lem_Reecos a

lemma lem_eacosalog2 (n : ℕ) (hn : n ≥ 1) (y : ℝ) : ((n : ℂ) ^ (-y * Complex.I)).re = Real.cos (-y * Real.log (n : ℝ)) := by
  rw [lem_niyelog n hn y]
  exact lem_eacosalog n hn y

lemma lem_eacosalog3 (n : ℕ) (hn : n ≥ 1) (y : ℝ) : ((n : ℂ) ^ (-y * Complex.I)).re = Real.cos (y * Real.log (n : ℝ)) := by
  rw [lem_eacosalog2 n hn y]
  exact lem_coseveny n hn y

lemma real_part_of_diff (M : ℝ) (w : ℂ) : (2 * M - w).re = 2 * M - w.re := by
  simp [Complex.sub_re]

lemma real_part_of_diffz (M : ℝ) (f_z : ℂ) : (2 * M - f_z).re = 2 * M - f_z.re := real_part_of_diff M f_z

lemma inequality_reversal (x M : ℝ) (hxM : x ≤ M) : 2 * M - x ≥ M := by linarith

lemma real_part_lower_bound (w : ℂ) (M : ℝ) (_hM : M > 0) (h : w.re ≤ M) : 2 * M - w.re ≥ M := by apply inequality_reversal w.re M h

lemma real_part_lower_bound3 (w : ℂ) (M : ℝ) (hM : M > 0) (h : w.re ≤ M) : (2 * M - w).re > 0 := by
  rw [real_part_of_diffz]
  apply lt_of_le_of_lt'
  apply real_part_lower_bound
  exact hM
  exact h
  exact hM

lemma nonzero_if_real_part_positive (w : ℂ) (hw_re_pos : w.re > 0) : w ≠ 0 := by
  by_contra h
  rw [h] at hw_re_pos
  exact lt_irrefl 0 hw_re_pos

lemma lem_real_part_lower_bound4 (w : ℂ) (M : ℝ) (hM : M > 0) (h : w.re ≤ M) : (2 * M - w) ≠ 0 := by
  apply nonzero_if_real_part_positive
  exact real_part_lower_bound3 w M hM h

lemma lem_abspos (z : ℂ) : z ≠ 0 → norm z > 0 := by
  intro h_ne_zero
  apply Real.sqrt_pos.mpr
  exact Complex.normSq_pos.mpr h_ne_zero

lemma lem_real_part_lower_bound5 (w : ℂ) (M : ℝ) (hM : M > 0) (h : w.re ≤ M) : norm (2 * M - w) > 0 := by
  apply lem_abspos
  exact lem_real_part_lower_bound4 w M hM h

lemma lem_wReIm (w : ℂ) : w = w.re + Complex.I * w.im := by
  apply Complex.ext
  simp
  simp

lemma lem_modulus_sq_ReImw (M : ℝ) (w : ℂ) : norm (2 * M - w) ^ 2 - norm w ^ 2 = 4 * M * (M - w.re) := by
  simp_rw [Complex.sq_norm]
  simp_rw [Complex.normSq_apply]
  simp [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma lem_modulus_sq_identity (M : ℝ) (w : ℂ) : norm (2 * M - w) ^ 2 - norm w ^ 2 = 4 * M * (M - w.re) := lem_modulus_sq_ReImw M w

lemma lem_nonnegative_product (M x : ℝ) (hM : M > 0) (hxM : x ≤ M) : 4 * M * (M - x) ≥ 0 := by
  have h_four_M_nonneg : 4 * M ≥ 0 := by linarith [hM]
  have h_diff_nonneg : M - x ≥ 0 := by linarith [hxM]
  apply mul_nonneg h_four_M_nonneg h_diff_nonneg

lemma lem_nonnegative_product2 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : 4 * M * (M - w.re) ≥ 0 := by
  apply lem_nonnegative_product
  exact hM
  exact hw_re_le_M

lemma lem_nonnegative_product3 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : norm (2 * M - w) ^ 2 - norm w ^ 2 ≥ 0 := by
  rw [lem_modulus_sq_identity]
  apply lem_nonnegative_product2
  exact hM
  exact hw_re_le_M

lemma lem_nonnegative_product4 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : norm (2 * M - w) ^ 2 ≥ norm w ^ 2 := by
  have h := lem_nonnegative_product3 M w hM hw_re_le_M
  linarith

lemma lem_nonnegative_product5 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : norm (2 * M - w) ≥ norm w := by
  have h_sq_ge : ‖2 * M - w‖ ^ 2 ≥ ‖w‖ ^ 2 := by
    apply lem_nonnegative_product4 M w hM hw_re_le_M
  rw [ge_iff_le] at h_sq_ge                                                

  apply (sq_le_sq₀ (norm_nonneg w) (norm_nonneg (2 * M - w))).mp
  exact h_sq_ge

lemma lem_nonnegative_product6 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : norm w ≤ norm (2 * M - w) := by apply lem_nonnegative_product5 M w hM hw_re_le_M

lemma lem_ineqmultr (a b c : ℝ) (hc : c > 0) (_ha : 0 ≤ a) (hab : a ≤ b) : a / c ≤ b / c := by
  apply div_le_div_of_nonneg_right
  exact hab
  linarith [hc]

lemma lem_ineqmultrbb (a b : ℝ) (hb : b > 0) (ha : 0 ≤ a) (hab : a ≤ b) : a / b ≤ 1 := by
  have h := lem_ineqmultr a b b hb ha hab
  rw [div_self (ne_of_gt hb)] at h
  exact h

lemma lem_nonnegative_product7 (M : ℝ) (w : ℂ) (_hM : M > 0) (h_abs_diff_pos : norm (2 * M - w) > 0) (h_abs_le_abs_diff : norm w ≤ norm (2 * M - w)) : norm w / norm (2 * M - w) ≤ 1 := by
                                                                                   
  have h_abs_w_nonneg : 0 ≤ ‖w‖ := norm_nonneg w

  apply lem_ineqmultrbb
  exact h_abs_diff_pos
  exact h_abs_w_nonneg
  exact h_abs_le_abs_diff

lemma lem_nonnegative_product8 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) (h_abs_le_abs_diff : norm w ≤
norm (2 * M - w)) : norm w / norm (2 * M - w) ≤ 1 := by
  apply lem_nonnegative_product7 M w
  exact hM
  apply lem_real_part_lower_bound5 w M hM hw_re_le_M
  exact h_abs_le_abs_diff

lemma lem_triangle_ineq (N G : ℂ) : norm (N + G) ≤ norm N + norm G := by
  exact norm_add_le N G

def ballDR (R : ℝ) : Set ℂ := Metric.ball (0 : ℂ) R

theorem analyticWithinAt_to_analyticAt_aux {f : ℂ → ℂ} {S : Set ℂ} {z : ℂ} (_hS : S ∈ nhds z)
  (p : FormalMultilinearSeries ℂ ℂ ℂ) (r : ENNReal) (_h_conv_on_inter : r ≤ p.radius) (_hr_pos : 0 < r)
  (hasSumt : ∀ {y : ℂ}, z + y ∈ insert z S → y ∈ Metric.eball 0 r → HasSum (fun n => (p n) fun _x => y) (f (z + y)))
  (ε : ℝ) (hε_pos : ε > 0) (h_ball_subset_S : Metric.ball z ε ⊆ S) :
  let r' := min r (ENNReal.ofReal ε);
  ∀ {y : ℂ}, y ∈ Metric.eball 0 r' → HasSum (fun n => (p n) fun _x => y) (f (z + y)) := by
  intro r' y hy
  apply hasSumt
  ·                            

    right                                              
    apply h_ball_subset_S
    rw [Metric.mem_ball]
                                      
    simp
                               
    have : y ∈ Metric.eball 0 (ENNReal.ofReal ε) := by
      apply Metric.eball_subset_eball (min_le_right r (ENNReal.ofReal ε)) hy

    have ε_nn : ENNReal.ofReal ε = ↑(ε.toNNReal) := by
      simp [ENNReal.ofReal]
    rw [ε_nn] at this
    rw [@Metric.eball_coe] at this
    simpa [Metric.mem_ball, dist_self_add_right, Real.toNNReal_of_nonneg hε_pos.le]

  ·                              
    exact Metric.eball_subset_eball (min_le_left r (ENNReal.ofReal ε)) hy

theorem analyticWithinAt_to_analyticAt {f : ℂ → ℂ} {S : Set ℂ} {z : ℂ}
    (hS : S ∈ nhds z) (h : AnalyticWithinAt ℂ f S z) : AnalyticAt ℂ f z := by
  rcases h with ⟨p, hp⟩

  use p

  rcases hp with ⟨r, h_conv_on_inter, hr_pos⟩

  rcases Metric.mem_nhds_iff.mp hS with ⟨ε, hε_pos, h_ball_subset_S⟩

  let r' := min r (ENNReal.ofReal ε)
  use r'

  constructor

  · exact inf_le_of_left_le h_conv_on_inter

  ·
    exact lt_min hr_pos (ENNReal.ofReal_pos.mpr hε_pos)
  rename_i hasSumt
  exact analyticWithinAt_to_analyticAt_aux hS p r h_conv_on_inter hr_pos hasSumt ε hε_pos h_ball_subset_S

lemma lem_1zanalDR (R : ℝ) (_hR_pos : 0 < R) :
    AnalyticOn ℂ (fun z ↦ z⁻¹) {z : ℂ | norm z ≤ R ∧ z ≠ 0} := by

  apply AnalyticOn.mono (analyticOn_inv)
                                                     
  intro z hz
                                                       
  exact hz.2

lemma lem_analprod {T : Set ℂ} {f1 f2 : ℂ → ℂ} (hf1 : AnalyticOn ℂ f1 T) (hf2 : AnalyticOn ℂ f2 T) :
    AnalyticOn ℂ (f1 * f2) T := by
  exact hf1.mul hf2

lemma lem_fzzTanal {R : ℝ} (hR_pos : 0 < R) (f : ℂ → ℂ)
    (hf : AnalyticOn ℂ f (Metric.closedBall 0 R)) :
    AnalyticOn ℂ (fun z ↦ f z / z) {z : ℂ | norm z ≤ R ∧ z ≠ 0} := by
                          
  rw [show (fun z ↦ f z / z) = (fun z ↦ f z) * (fun z ↦ z⁻¹) by ext; simp [div_eq_mul_inv]]
                                
  let T := {z : ℂ | norm z ≤ R ∧ z ≠ 0}
                                                            
  have hf_on_T : AnalyticOn ℂ f T := hf.mono (?_)
                         
  have h_inv_on_T : AnalyticOn ℂ (fun z ↦ z⁻¹) T := lem_1zanalDR R hR_pos
                                                                
  exact lem_analprod hf_on_T h_inv_on_T
  intro z hz
  have hT : T = {z | norm z ≤ R ∧ z ≠ 0} := rfl
  rw [hT] at hz
  simp only [Set.mem_ofPred_eq] at hz
  simp only [Metric.mem_closedBall]
  simp only [dist_zero_right]
  exact hz.1

lemma lem_AnalOntoWithin {V : Set ℂ} {h : ℂ → ℂ} (hh : AnalyticOn ℂ h V) (z : ℂ) (hz : z ∈ V) :
    AnalyticWithinAt ℂ h V z := by
  exact hh z hz

lemma lem_DR0T {R : ℝ} (hR : 0 < R) :
    Metric.closedBall 0 R = {0} ∪ {z : ℂ | norm z ≤ R ∧ z ≠ 0} := by
  ext z
  simp [Metric.closedBall, dist_zero_right]
  by_cases hz : z = 0
  · simp [hz, hR.le]
  · simp [hz]

lemma lem_analWWWithin {R : ℝ} (hR_pos : 0 < R) (h : ℂ → ℂ) :
    (AnalyticWithinAt ℂ h (Metric.closedBall 0 R) 0) →
    (∀ z ∈ {z : ℂ | norm z ≤ R ∧ z ≠ 0}, AnalyticWithinAt ℂ h (Metric.closedBall 0 R) z) →
    (∀ z ∈ Metric.closedBall 0 R, AnalyticWithinAt ℂ h (Metric.closedBall 0 R) z) := by
  intro h0 hT z hz
  rw [lem_DR0T hR_pos] at hz
  cases' hz with hz hz
  · simp at hz
    rw [hz]
    exact h0
  · exact hT z hz

lemma lem_analWWithinAtOn (R : ℝ) (hR_pos : 0 < R) (h : ℂ → ℂ)
    (h_at_0 : AnalyticWithinAt ℂ h (Metric.closedBall 0 R) 0)
    (h_at_T : ∀ z ∈ {z : ℂ | norm z ≤ R ∧ z ≠ 0}, AnalyticWithinAt ℂ h (Metric.closedBall 0 R) z) :
    AnalyticOn ℂ h (Metric.closedBall 0 R) := by
  exact lem_analWWWithin hR_pos h h_at_0 h_at_T

lemma lem_AnalAttoWithin {h : ℂ → ℂ} {s : Set ℂ} (hh : AnalyticAt ℂ h 0) :
    AnalyticWithinAt ℂ h s 0 := by
  exact hh.analyticWithinAt

lemma analyticWithinAt_punctured_to_closedBall {R : ℝ} (_hR : 0 < R) {h : ℂ → ℂ} {z : ℂ} (hz : z ∈ {w : ℂ | norm w ≤ R ∧ w ≠ 0}) (h_within : AnalyticWithinAt ℂ h {w : ℂ | norm w ≤ R ∧ w ≠ 0} z) : AnalyticWithinAt ℂ h (Metric.closedBall 0 R) z := by
                                                                                                                   
  apply AnalyticWithinAt.mono_of_mem_nhdsWithin h_within

  have hz_ne_zero : z ≠ 0 := hz.2

  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]

  use Metric.ball z (‖z‖ / 2)

  constructor
  ·                                      
    exact Metric.ball_mem_nhds z (half_pos (norm_pos_iff.mpr hz_ne_zero))

  ·                                                                                       
    intro w hw
    constructor
    ·                   
      have w_in_closedball : w ∈ Metric.closedBall 0 R := hw.2
      simp only [Metric.mem_closedBall, dist_zero_right] at w_in_closedball
                                           
      simp [w_in_closedball]
    ·              
      intro hw_eq_zero
      have w_in_ball : w ∈ Metric.ball z (‖z‖ / 2) := hw.1
      rw [hw_eq_zero] at w_in_ball
      simp only [Metric.mem_ball] at w_in_ball

      rw [dist_comm] at w_in_ball
      simp at w_in_ball
      have pos_norm : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne_zero
      linarith [pos_norm]

lemma lem_analAtOnOn {R : ℝ} (hR_pos : 0 < R) (h : ℂ → ℂ) :
    AnalyticAt ℂ h 0 →
    AnalyticOn ℂ h {z : ℂ | norm z ≤ R ∧ z ≠ 0} →
    AnalyticOn ℂ h (Metric.closedBall 0 R) := by
  intro h_at_0 h_on_punctured

  apply lem_analWWithinAtOn R hR_pos h

  · exact lem_AnalAttoWithin h_at_0

  · intro z hz
                                                       
    have h_within_punctured : AnalyticWithinAt ℂ h {w : ℂ | norm w ≤ R ∧ w ≠ 0} z :=
      lem_AnalOntoWithin h_on_punctured z hz
                                     
    exact analyticWithinAt_punctured_to_closedBall hR_pos hz h_within_punctured

lemma lem_orderne0 (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0) :
    analyticOrderAt f 0 ≠ 0 := by exact (AnalyticAt.analyticOrderAt_ne_zero hf).mpr hf0

lemma lem_ordernetop (f : ℂ → ℂ) (_hf : AnalyticAt ℂ f 0) (hf_ne_zero : ¬(∀ᶠ z in nhds 0, f z = 0)) :
    analyticOrderAt f 0 ≠ ⊤ := by
  intro h
  rw [analyticOrderAt_eq_top] at h
  exact hf_ne_zero h

lemma lem_ordernatcast (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (n : ℕ) (hn : analyticOrderAt f 0 = n) :
    ∃ (g : ℂ → ℂ), AnalyticAt ℂ g 0 ∧ g 0 ≠ 0 ∧ ∀ᶠ (z : ℂ) in nhds 0, f z = z ^ n * g z := by

  rw [AnalyticAt.analyticOrderAt_eq_natCast] at hn
  · convert (preTransparency := .instances) hn
    aesop
  · exact hf

lemma lem_ordernatcast1 (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (n : ℕ) (hn : analyticOrderAt f 0 = n) (hn_ne_zero : n ≠ 0) :
    ∃ (h : ℂ → ℂ), AnalyticAt ℂ h 0 ∧ ∀ᶠ z in nhds 0, f z = z * h z := by
                           
  rcases lem_ordernatcast f hf n hn with ⟨g, hg_analytic, _, hf_eq_g⟩
                              
  use fun z ↦ z ^ (n - 1) * g z
  constructor
  ·                                                    
    exact (analyticAt_id.pow (n - 1)).mul hg_analytic
  ·                        
    filter_upwards [hf_eq_g] with z h_eq
    rw [h_eq]
    ring_nf
    rw [← pow_succ' z (n - 1), Nat.sub_add_cancel (Nat.pos_of_ne_zero hn_ne_zero)]

lemma lem_ordernatcast2_old (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0)
    (h_not_eventually_zero : ¬ (∀ᶠ z in nhds 0, f z = 0)) :
    ∃ (h : ℂ → ℂ), AnalyticAt ℂ h 0 ∧ ∀ᶠ z in nhds 0, f z = z * h z := by
                                 
  let n₀ := analyticOrderAt f 0
                                                                        
  have hn_ne_top : n₀ ≠ ⊤ := lem_ordernetop f hf h_not_eventually_zero
                                             
  lift n₀ to ℕ using hn_ne_top with n hn_eq
                                                  
  have hn_ne_zero : n ≠ 0 := by
    intro hn_zero
    rw [hn_zero] at hn_eq

    have t := (lem_orderne0 f hf hf0)
    have : n₀ = analyticOrderAt f 0 := rfl
    rw [←this] at t
    exact t (id (Eq.symm hn_eq))
                                                                       
  exact lem_ordernatcast1 f hf n (by aesop) hn_ne_zero

lemma lem_ordernatcast2 {R : ℝ} (hR_pos : 0 < R) (f : ℂ → ℂ) (hf0 : f 0 = 0)
    (hf : AnalyticOn ℂ f (Metric.closedBall 0 R)) :
    AnalyticAt ℂ (fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z) 0 := by
                                                                            
  have hS : Metric.closedBall 0 R ∈ nhds (0 : ℂ) := by
                                                              
    refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℂ) hR_pos) ?subset
    exact Metric.ball_subset_closedBall
  have hf_within : AnalyticWithinAt ℂ f (Metric.closedBall 0 R) 0 := hf 0 (by
    simp [Metric.mem_closedBall, hR_pos.le])
  have hf_at0 : AnalyticAt ℂ f 0 := analyticWithinAt_to_analyticAt hS hf_within

  let g : ℂ → ℂ := fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z

  by_cases hEZ : (∀ᶠ z in nhds (0 : ℂ), f z = 0)
  ·                                                                                          
                                          
    have hU : {z : ℂ | f z = 0} ∈ nhds (0 : ℂ) := by simpa only [Filter.Eventually] using hEZ
                                        
    have hf_eq_zero : f =ᶠ[nhds (0 : ℂ)] (fun _ : ℂ => 0) := by
      refine (Filter.eventuallyEq_iff_exists_mem).2 ?_
      exact ⟨{z | f z = 0}, hU, by intro z hz; simpa [Set.mem_ofPred_eq] using hz⟩
                                                                    
    have h_fderiv_zero : (fderiv ℂ f 0) = 0 := by
      simpa using (Filter.EventuallyEq.fderiv_eq hf_eq_zero)

    have h_g_zero_on_U : ∀ z ∈ {z : ℂ | f z = 0}, g z = 0 := by
      intro z hzU
      by_cases hz0 : z = 0
      ·                                  
        simp [g, hz0, h_fderiv_zero]
      ·                                  
        have : f z = 0 := by simpa [Set.mem_ofPred_eq] using hzU
        simp [g, hz0, this]
                                                                                  
    have h_const0_within : AnalyticWithinAt ℂ (fun _ : ℂ => (0 : ℂ)) {z : ℂ | f z = 0} 0 :=
      analyticAt_const.analyticWithinAt
    have h_g_within : AnalyticWithinAt ℂ g {z : ℂ | f z = 0} 0 := by
                                        
      apply h_const0_within.congr
      intro z hz
      by_cases hz0 : z = 0
      ·        
        simp [g, hz0, h_fderiv_zero]
      ·             
        have : f z = 0 := by simpa [Set.mem_ofPred_eq] using hz
        simp [g, hz0, this]
                           
      simp [g, h_fderiv_zero]
    exact analyticWithinAt_to_analyticAt hU h_g_within

  ·                                                                
    have h_notEZ : ¬ (∀ᶠ z in nhds (0 : ℂ), f z = 0) := hEZ
                                                        
    rcases lem_ordernatcast2_old f hf_at0 hf0 h_notEZ with ⟨h0, h0_at0, hfac_ev⟩
                                                               
    have hV : {z : ℂ | f z = z * h0 z} ∈ nhds (0 : ℂ) := by simpa only [Filter.Eventually] using hfac_ev
    have h_eq_nhds : f =ᶠ[nhds (0 : ℂ)] (fun z => z * h0 z) :=
      (Filter.eventuallyEq_iff_exists_mem).2 ⟨{z : ℂ | f z = z * h0 z}, hV, by
        intro z hz; simpa [Set.mem_ofPred_eq] using hz⟩
                              
    have h_fderiv_prod : fderiv ℂ f 0 = fderiv ℂ (fun z => z * h0 z) 0 :=
      Filter.EventuallyEq.fderiv_eq h_eq_nhds
                                                                              
    have h_diff_id : DifferentiableAt ℂ (fun z : ℂ => z) 0 := differentiableAt_id
    have h_diff_h0 : DifferentiableAt ℂ h0 0 := h0_at0.differentiableAt
                             
    have h_val0 : (fderiv ℂ f 0) 1 = h0 0 := by
                                                           
      rw [h_fderiv_prod]
      rw [fderiv_fun_mul' h_diff_id h_diff_h0]
      simp only [add_apply, smul_apply]
      rw [fderiv_fun_id]
      simp only [ContinuousLinearMap.id_apply]
      simp only [zero_smul, zero_add]
      simp

    have h_geq_h0_on_V : ∀ z ∈ {z : ℂ | f z = z * h0 z}, g z = h0 z := by
      intro z hzU
      by_cases hz0 : z = 0
      ·        
        simpa [g, hz0] using h_val0
      ·                                    
        have : f z = z * h0 z := by simpa [Set.mem_ofPred_eq] using hzU
        simp only [g, if_neg hz0, this]
        exact mul_div_cancel_left₀ (h0 z) hz0
                                                                    
    have h0_within : AnalyticWithinAt ℂ h0 {z : ℂ | f z = z * h0 z} 0 := h0_at0.analyticWithinAt
    have hg_within : AnalyticWithinAt ℂ g {z : ℂ | f z = z * h0 z} 0 := by

      apply AnalyticWithinAt.congr h0_within
                                 
      intro z hz
      exact h_geq_h0_on_V z hz

      have h_0_in_V : (0 : ℂ) ∈ {z : ℂ | f z = z * h0 z} := by
        simp [hf0]
      exact h_geq_h0_on_V 0 h_0_in_V
    exact analyticWithinAt_to_analyticAt hV hg_within

lemma lem_ballDR (R : ℝ) (hR : R > 0) : closure (ballDR R) = Metric.closedBall (0 : ℂ) R := by
  unfold ballDR
  exact closure_ball 0 (ne_of_gt hR)

lemma lem_inDR (R : ℝ) (hR : R > 0) (w : ℂ) (hw : w ∈ closure (ballDR R)) : norm w ≤ R := by
  rw [lem_ballDR R hR] at hw
  rw [Metric.mem_closedBall] at hw
  rw [Complex.dist_eq] at hw
  simp at hw
  exact hw

lemma lem_notinDR (R : ℝ) (_hR : R > 0) (w : ℂ) (hw : w ∉ ballDR R) : norm w ≥ R := by
                               
  unfold ballDR at hw
                                                   
  rw [Metric.mem_ball] at hw
                                                              
  push Not at hw
                                                                     
  rw [Complex.dist_eq] at hw
                       
  simp at hw
  exact hw

lemma lem_legeR (R : ℝ) (_hR : R > 0) (w : ℂ) (hw1 : norm w ≤ R) (hw2 : norm w ≥ R) : norm w = R := by
  linarith

lemma lem_circleDR (R : ℝ) (hR : R > 0) (w : ℂ) (hw1 : w ∈ closure (ballDR R)) (hw2 : w ∉ ballDR R) : norm w = R := by
  have h1 : norm w ≤ R := lem_inDR R hR w hw1
  have h2 : norm w ≥ R := lem_notinDR R hR w hw2
  exact lem_legeR R hR w h1 h2

lemma lem_Rself (R : ℝ) (hR : R > 0) : |R| = R := by
  rw [abs_eq_self]
  linarith

lemma lem_Rself2 (R : ℝ) (hR : R > 0) : |R| ≤ R := by
  rw [lem_Rself R hR]

lemma lem_Rself3 (R : ℝ) (hR : R > 0) : (R : ℂ) ∈ closure (ballDR R) := by
  rw [lem_ballDR R hR]
  rw [Metric.mem_closedBall]
  simp
  exact lem_Rself2 R hR

lemma lem_DRcompact (R : ℝ) (hR : R > 0) : IsCompact (closure (ballDR R)) := by
  rw [lem_ballDR R hR]
  apply Metric.isCompact_of_isClosed_isBounded
  · exact Metric.isClosed_closedBall
  · exact Metric.isBounded_closedBall

lemma lem_ExtrValThm {K : Set ℂ} (hK : IsCompact K) (hK_nonempty : K.Nonempty) (g : K → ℂ) (hg : Continuous g) :
∃ v : K, ∀ z : K, norm (g z) ≤ norm (g v) := by
                                       
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
                            
  have : Nonempty K := hK_nonempty.to_subtype
                                                             
  let f : K → ℝ := fun z => norm (g z)
                                
  have hf_cont : Continuous f := continuous_norm.comp hg
                                                       
  obtain ⟨v, hv_mem, hv_max⟩ := IsCompact.exists_isMaxOn isCompact_univ Set.univ_nonempty hf_cont.continuousOn
  use v
  intro z
  exact hv_max (Set.mem_univ z)

lemma lem_ExtrValThmDR (R : ℝ) (hR : R > 0) (g : closure (ballDR R) → ℂ) (hg : Continuous g) :
∃ v : closure (ballDR R), ∀ z : closure (ballDR R), norm (g z) ≤ norm (g v) := by
                                                     
  have hK_compact : IsCompact (closure (ballDR R)) := lem_DRcompact R hR
                                             
  have hK_nonempty : (closure (ballDR R)).Nonempty := by
    rw [lem_ballDR R hR]
    rw [Metric.nonempty_closedBall]
    linarith
                                    
  exact lem_ExtrValThm hK_compact hK_nonempty g hg

lemma lem_AnalCont {R : ℝ} (_hR : R > 0) (H : ℂ → ℂ) (h_analytic : AnalyticOn ℂ H (closure (ballDR R))) :
Continuous (H ∘ (Subtype.val : closure (ballDR R) → ℂ)) := by
                                                                    
  have h_cont_on : ContinuousOn H (closure (ballDR R)) := AnalyticOn.continuousOn h_analytic
                              
  have h_val_cont : Continuous (Subtype.val : closure (ballDR R) → ℂ) := continuous_subtype_val

  exact ContinuousOn.comp_continuous h_cont_on h_val_cont (fun _ => Subtype.mem _)

lemma lem_ExtrValThmh {R : ℝ} (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) :
∃ u : closure (ballDR R), ∀ z : closure (ballDR R), norm (h u) ≥ norm (h z) := by
                                                    
  have hg_continuous : Continuous (h ∘ Subtype.val : closure (ballDR R) → ℂ) :=
    lem_AnalCont hR h h_analytic
                                              
  obtain ⟨v, hv⟩ := lem_ExtrValThmDR R hR (h ∘ Subtype.val) hg_continuous
                   
  use v
                                        
  intro z
  have : norm ((h ∘ Subtype.val) z) ≤ norm ((h ∘ Subtype.val) v) := hv z
                             
  simp [Function.comp] at this
  exact this

lemma lem_MaxModP (R : ℝ) (_hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) (w : ℂ) (hw_in_DR : w ∈ ballDR R) (hw_max : ∀ z ∈ ballDR R, norm (h z) ≤ norm (h w)) : ∀ z ∈ closure (ballDR R), norm (h z) = norm (h w) := by
                                                             
  have h_preconnected : IsPreconnected (ballDR R) := by
    unfold ballDR
    apply Convex.isPreconnected
    exact convex_ball (0 : ℂ) R

  have h_open : IsOpen (ballDR R) := by
    unfold ballDR
    exact Metric.isOpen_ball

  have h_diff_cont : DiffContOnCl ℂ h (ballDR R) := by
    constructor
    ·                                   
      apply AnalyticOn.differentiableOn
      exact h_analytic.mono subset_closure
    ·                                         
      exact AnalyticOn.continuousOn h_analytic

  have h_max_on : IsMaxOn (norm ∘ h) (ballDR R) w := by
    intro z hz
    change ‖h z‖ ≤ ‖h w‖
    exact hw_max z hz

  have h_eq := Complex.norm_eqOn_closure_of_isPreconnected_of_isMaxOn h_preconnected h_open h_diff_cont hw_in_DR h_max_on

  intro z hz
  have norm_eq := h_eq hz
  simp only [Function.comp_apply, Function.const_apply] at norm_eq
                                                                                   
  convert (preTransparency := .instances) norm_eq

lemma lem_MaxModR (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) (w : ℂ) (hw_in_DR : w ∈ ballDR R) (hw_max : ∀ z ∈ ballDR R, norm (h z) ≤ norm (h w)) : norm (h R) = norm (h w) := by
                                                                
  have h_const : ∀ z ∈ closure (ballDR R), norm (h z) = norm (h w) :=
    lem_MaxModP R hR h h_analytic w hw_in_DR hw_max
                                                      
  have hR_in_closure : (R : ℂ) ∈ closure (ballDR R) := lem_Rself3 R hR
                                         
  exact h_const (R : ℂ) hR_in_closure

lemma lem_MaxModRR (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (w : ℂ) (hw_in_DR : w ∈ ballDR R) (hw_max : ∀ z ∈ ballDR R, norm (h z) ≤ norm (h w)) :
∀ z ∈ closure (ballDR R), norm (h R) ≥ norm (h z) := by
  intro z hz
                                                                            
  have h1 := lem_MaxModP R hR h h_analytic w hw_in_DR hw_max z hz
                                             
  have h2 := lem_MaxModR R hR h h_analytic w hw_in_DR hw_max
                                                                             
  rw [h2, h1]

theorem lem_MaxModv2 (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) :
∃ v : closure (ballDR R), norm (v : ℂ) = R ∧ ∀ z : closure (ballDR R), norm (h (v : ℂ)) ≥ norm (h (z : ℂ)) := by
                                                       
  obtain ⟨u, hu⟩ := lem_ExtrValThmh hR h h_analytic

  if h_case : (u : ℂ) ∈ ballDR R then
                                 
    have hR_in_closure : (R : ℂ) ∈ closure (ballDR R) := lem_Rself3 R hR
    let v : closure (ballDR R) := ⟨R, hR_in_closure⟩
    use v
    constructor
    ·                
                                                                             
      have v_eq : (v : ℂ) = (R : ℂ) := rfl
      rw [v_eq]
                                                                               
      have : norm (R : ℂ) = abs R := by
        simp [Complex.norm_real]
      rw [this, lem_Rself R hR]
    ·                                                     
      intro z
                                                                        
      have hw_max : ∀ w ∈ ballDR R, norm (h w) ≤ norm (h (u : ℂ)) := by
        intro w hw
                                                      
        have hw_closure : w ∈ closure (ballDR R) := subset_closure hw
                                              
        let w_sub : closure (ballDR R) := ⟨w, hw_closure⟩
        exact hu w_sub
                                             
      have h_result := lem_MaxModRR R hR h h_analytic (u : ℂ) h_case hw_max
                                                  
      have v_eq : (v : ℂ) = (R : ℂ) := rfl
      rw [v_eq]
                                                           
      exact h_result (z : ℂ) (Subtype.mem z)
  else
                                 
    use u
    constructor
    ·                                   
      exact lem_circleDR R hR (u : ℂ) (Subtype.mem u) h_case
    ·                                                                  
      exact hu

theorem lem_MaxModv3 (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) :
∃ v : ℂ, norm v = R ∧ ∀ z : ℂ, z ∈ closure (ballDR R) → norm (h v) ≥ norm (h z) := by
                                                                                   
  obtain ⟨v_sub, hv_abs, hv_max⟩ := lem_MaxModv2 R hR h h_analytic
                                                           
  let v := (v_sub : ℂ)
  use v
  constructor
  ·                
    exact hv_abs
  ·                            
    intro z hz
                                               
    have hz_sub : z ∈ closure (ballDR R) := hz
    let z_sub : closure (ballDR R) := ⟨z, hz_sub⟩
    have := hv_max z_sub
                             
    simp at this
    exact this

lemma lem_MaxModv4 (R B : ℝ) (hR : R > 0) (_hB : B ≥ 0)
  (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (h_boundary_bound : ∀ z : ℂ, norm z = R → norm (h z) ≤ B) :
∃ v : ℂ, norm v = R ∧ (∀ w : ℂ, w ∈ closure (ballDR R) → norm (h v) ≥ norm (h w)) ∧ norm (h v) ≤ B := by
                                                                             
  obtain ⟨v, hv_abs, hv_max⟩ := lem_MaxModv3 R hR h h_analytic
                         
  use v
  constructor
  ·           
    exact hv_abs
  constructor
  ·                                                  
    exact hv_max
  ·                                                  
    apply h_boundary_bound
    exact hv_abs

lemma lem_HardMMP (R B : ℝ) (hR : R > 0) (hB : B ≥ 0)
  (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (h_boundary_bound : ∀ z : ℂ, norm z = R → norm (h z) ≤ B) :
∀ w : ℂ, w ∈ closure (ballDR R) → norm (h w) ≤ B := by
  intro w hw
                                                                                            
  obtain ⟨v, hv_abs, hv_max, hv_bound⟩ := lem_MaxModv4 R B hR hB h h_analytic h_boundary_bound
                                
  have h1 : norm (h w) ≤ norm (h v) := hv_max w hw
  have h2 : norm (h v) ≤ B := hv_bound
                             
  linarith [h1, h2]

lemma lem_EasyMMP (R B : ℝ) (hR : R > 0) (_hB : B ≥ 0)
  (h : ℂ → ℂ) (_h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (h_closure_bound : ∀ w : ℂ, w ∈ closure (ballDR R) → norm (h w) ≤ B) :
∀ z : ℂ, norm z = R → norm (h z) ≤ B := by
  intro z hz
                                                  
  apply h_closure_bound z
                                     
  rw [lem_ballDR R hR]
  rw [Metric.mem_closedBall]
  rw [Complex.dist_eq]
  simp

  have : ‖z‖ = R := hz
  linarith

theorem lem_MMP (R B : ℝ) (hR : R > 0) (hB : B ≥ 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) :
(∀ z : ℂ, z ∈ closure (ballDR R) → norm (h z) ≤ B) ↔ (∀ z : ℂ, norm z = R → norm (h z) ≤ B) := by
  constructor
  ·                                                     
    intro h_closure_bound
    exact lem_EasyMMP R B hR hB h h_analytic h_closure_bound
  ·                                                      
    intro h_boundary_bound
    exact lem_HardMMP R B hR hB h h_analytic h_boundary_bound

lemma lem_denominator_nonzero (R M : ℝ) (_hR : R > 0) (hM : M > 0)
  (f : ℂ → ℂ) (_h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
  (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M) :
∀ z : ℂ, z ∈ closure (ballDR R) → (2 * M - f z) ≠ 0 := by
  intro z hz
                                                  
  apply lem_real_part_lower_bound4 (f z) M hM
                                   
  exact h_re_bound z hz

lemma lem_removable_singularity (R : ℝ) (hR : R > 0) (f : ℂ → ℂ)
  (h_analytic : AnalyticOn ℂ f (closure (ballDR R))) (h_zero : f 0 = 0) :
AnalyticOn ℂ (fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z) (closure (ballDR R)) := by
                                                                             
  rw [lem_ballDR R hR] at h_analytic ⊢

  let g : ℂ → ℂ := fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z

  apply lem_analAtOnOn hR g

  ·                                
                                                   
    exact lem_ordernatcast2 hR f h_zero h_analytic

  ·                                                         

    have f_on_closedball : AnalyticOn ℂ f (Metric.closedBall 0 R) := h_analytic
    have quotient_analytic : AnalyticOn ℂ (fun z ↦ f z / z) {z : ℂ | ‖z‖ ≤ R ∧ z ≠ 0} :=
      lem_fzzTanal hR f f_on_closedball

    apply AnalyticOn.congr quotient_analytic
    intro z hz
                                                                 
    simp [g, if_neg hz.2]

lemma lem_quotient_analytic {R : ℝ} (_hR : R > 0) (h1 h2 : ℂ → ℂ)
  (h_analytic1 : AnalyticOn ℂ h1 (closure (ballDR R)))
  (h_analytic2 : AnalyticOn ℂ h2 (closure (ballDR R)))
  (h_nonzero : ∀ z ∈ closure (ballDR R), h2 z ≠ 0) :
AnalyticOn ℂ (fun z ↦ h1 z / h2 z) (closure (ballDR R)) := by
  exact AnalyticOn.div h_analytic1 h_analytic2 h_nonzero

noncomputable def f_M (R M : ℝ) (_hR : R > 0) (_hM : M > 0)
    (f : ℂ → ℂ)
    (_h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (_h_zero : f 0 = 0)
    (_h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M) :
ℂ → ℂ := fun z ↦ (if z = 0 then (fderiv ℂ f 0) 1 else f z / z) / (2 * M - f z)

lemma lem_g_analytic (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M) :
AnalyticOn ℂ (f_M R M hR hM f h_analytic h_zero h_re_bound) (closure (ballDR R)) := by
                                                          
  let h₁ : ℂ → ℂ := fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z
                              
  let h₂ : ℂ → ℂ := fun z ↦ 2 * M - f z

  have h_eq : f_M R M hR hM f h_analytic h_zero h_re_bound = fun z ↦ h₁ z / h₂ z := by
    ext z
    unfold f_M h₁ h₂
    simp

  rw [h_eq]

  apply lem_quotient_analytic hR

  · exact lem_removable_singularity R hR f h_analytic h_zero

  · have h₂_analytic : AnalyticOn ℂ h₂ (closure (ballDR R)) := by
      unfold h₂
      apply AnalyticOn.sub
      · exact analyticOn_const
      · exact h_analytic
    exact h₂_analytic

  · intro z hz
    unfold h₂
    exact lem_denominator_nonzero R M hR hM f h_analytic h_re_bound z hz

lemma lem_absab (a b : ℂ) (_hb : b ≠ 0) : norm (a / b) = norm a / norm b := by
  exact IsAbsoluteValue.abv_div norm a b

lemma lem_g_on_boundaryz (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (z : ℂ) (hz_in_closure : z ∈ closure (ballDR R)) (hz_nonzero : z ≠ 0) :
  norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
norm (f z / z) / norm (2 * M - f z) := by
                              
  unfold f_M
                                                                
  simp only [if_neg hz_nonzero]

  have h_nonzero : (2 * M - f z) ≠ 0 := lem_denominator_nonzero R M hR hM f h_analytic h_re_bound z hz_in_closure
                    
  exact lem_absab (f z / z) (2 * M - f z) h_nonzero

lemma lem_fzzR (R : ℝ) (hR : R > 0) (z w : ℂ) (hz : norm z = R) : norm (w / z) = norm w / R := by
                          
  have hz_nonzero : z ≠ 0 := by
    intro h_eq
    rw [h_eq] at hz
    simp at hz
    linarith [hz, hR]
                    
  rw [lem_absab w z hz_nonzero]
                               
  rw [hz]

lemma lem_g_at_r (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_on_boundary : norm z = r) :
  norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
(norm (f z) / r) / norm (2 * M - f z) := by
                                            
  have hz_nonzero : z ≠ 0 := by
    intro h_eq
    rw [h_eq] at hz_on_boundary
    simp at hz_on_boundary
    linarith [hz_on_boundary, hr_pos]

  have hz_in_closure : z ∈ closure (ballDR R) := by
    rw [lem_ballDR R hR]
    rw [Metric.mem_closedBall]
    rw [Complex.dist_eq]
    simp
    linarith [hz_on_boundary, hr_lt_R]

  have h1 : norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
    norm (f z / z) / norm (2 * M - f z) :=
    lem_g_on_boundaryz R M hR hM f h_analytic h_zero h_re_bound z hz_in_closure hz_nonzero

  have h2 : norm (f z / z) = norm (f z) / r :=
    lem_fzzR r hr_pos z (f z) hz_on_boundary

  rw [h1, h2]

lemma lem_fracs (a b r R : ℝ) (ha : a > 0) (hb : b > 0) (hr : r > 0) (hR : R > 0)
(h_le : (a / r) / b ≤ 1 / R) : R * a ≤ r * b := by
                                              
  have h1 : (a / r) / b = a / (r * b) := by
    field_simp
  rw [h1] at h_le

  have h_pos_rb : 0 < r * b := mul_pos hr hb
  rw [div_le_div_iff₀ h_pos_rb hR] at h_le
                                      
  simp only [one_mul] at h_le

  linarith

def I := Complex.I

lemma lem_modeit (t : ℝ) : norm (Complex.exp (I * t)) = Real.exp (Complex.re (I * t)) := by
                                                        
  exact Complex.norm_exp (I * t)

lemma lem_Reit0 (t : ℝ) : Complex.re (I * t) = 0 := by
                                        
  unfold I
                                                    
  rw [Complex.mul_re]

  rw [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
                                  
  ring

lemma lem_e01 : Real.exp 0 = 1 := by
  exact Real.exp_zero

lemma lem_modulus_of_e_it_is_one (t : ℝ) : norm (Complex.exp (I * t)) = 1 := by
                                                                                            
  rw [lem_modeit]
                                                   
  rw [lem_Reit0]
                                         
  rw [lem_e01]

lemma lem_modulus_of_ae_it {a t : ℝ} (ha : 0 < a) : norm (a * Complex.exp (I * t)) = a := by
                                                              
  rw [norm_mul, lem_modulus_of_e_it_is_one, mul_one, Complex.norm_real]
  exact abs_of_pos ha

lemma lem_reverse_triangle (w z : ℂ) : norm w - norm z ≤ norm (w - z) := by

  exact norm_sub_norm_le w z

lemma lem_reverse_triangle3 {R_analytic r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (_h_r_int_lt_R_analytic : r_int < R_analytic) :
r_int - norm z ≤ norm (r_int * Complex.exp (I * t) - z) := by
                                                  
  have h_mod : norm (r_int * Complex.exp (I * t)) = r_int := by
    have h_r_int_pos : 0 < r_int := lt_trans h_r_z_pos h_r_z_lt_r_int
    exact lem_modulus_of_ae_it h_r_int_pos
                                                                    
  have h_triangle := lem_reverse_triangle (r_int * Complex.exp (I * t)) z
                                     
  rw [h_mod] at h_triangle
  exact h_triangle

lemma lem_zrr1 {R_analytic r_z r_int : ℝ}
    (_h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (_h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
0 < r_int - norm z := by
                                                      
  have h1 : dist z 0 ≤ r_z := Metric.mem_closedBall.mp hz
                                        
  have h2 : dist z 0 = ‖z‖ := by
    rw [dist_eq_norm, sub_zero]
                 
  have h3 : ‖z‖ ≤ r_z := by rwa [← h2]
                                      
  have h4 : norm z = ‖z‖ := rfl
                    
  have h5 : norm z ≤ r_z := by rwa [h4]
                                                     
  have h6 : norm z < r_int := lt_of_le_of_lt h5 h_r_z_lt_r_int
                                 
  linarith

lemma lem_reverse_triangle4 {R_analytic r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hz : z ∈ Metric.closedBall 0 r_z) :
0 < norm (r_int * Complex.exp (I * t) - z) := by
                                             
  have h1 := lem_zrr1 h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
                                                                                               
  have h2 := @lem_reverse_triangle3 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic
                               
  exact lt_of_lt_of_le h1 h2

lemma lem_wposneq0 (w : ℂ) : norm w > 0 → w ≠ 0 := by
  intro h
                                                  
  by_contra h_eq_zero
                              
  have h_abs_zero : norm w = 0 := by
    rw [h_eq_zero]
    simp
                                        
  rw [h_abs_zero] at h
  exact lt_irrefl 0 h

lemma lem_reverse_triangle5 {R_analytic r_z r_int : ℝ} (t : ℝ)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
r_int * Complex.exp (I * t) - z ≠ 0 := by
                                                                                  
  have h_pos := @lem_reverse_triangle4 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
                                                                  
  exact lem_wposneq0 (r_int * Complex.exp (I * t) - z) h_pos

lemma lem_reverse_triangle6 {R_analytic r_z r_int : ℝ} (t : ℝ)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
(r_int * Complex.exp (I * t) - z) ^ 2 ≠ 0 := by
                                                                   
  have h_ne_zero := lem_reverse_triangle5 t h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
                                                                                    
  exact pow_ne_zero 2 h_ne_zero

lemma continuous_real_parameterization (r : ℝ) : Continuous (fun t : ℝ => r * Complex.exp (I * t)) := by

  have h1 : Continuous (fun t : ℝ => (t : ℂ)) := Complex.continuous_ofReal

  have h2 : Continuous (fun z : ℂ => I * z) := by
    apply Continuous.mul
    · exact continuous_const
    · exact continuous_id

  have h3 : Continuous Complex.exp := Complex.continuous_exp

  have h4 : Continuous (fun z : ℂ => (r : ℂ) * z) := by
    apply Continuous.mul
    · exact continuous_const
    · exact continuous_id

  apply Continuous.comp h4
  apply Continuous.comp h3
  apply Continuous.comp h2
  exact h1

lemma continuous_f_parameterized {f : ℂ → ℂ} {R r : ℝ}     (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R ⊆ U ∧ DifferentiableOn ℂ f U)
 (hr_pos : 0 < r) (hr_lt_R : r < R) : Continuous (fun t : ℝ => f (r * Complex.exp (I * t))) := by
                                                                       
  obtain ⟨U', hU'_open, h_subset, hf_diff_U'⟩ := hf_domain
  have hf_cont : ContinuousOn f (Metric.closedBall 0 R) := by
                                                                  
    have hf_on_closed : DifferentiableOn ℂ f (Metric.closedBall 0 R) :=
      hf_diff_U'.mono h_subset
                                                               
    exact DifferentiableOn.continuousOn hf_on_closed

  have hparam_cont : Continuous (fun t : ℝ => r * Complex.exp (I * t)) := continuous_real_parameterization r

  have hparam_range : ∀ t : ℝ, r * Complex.exp (I * t) ∈ Metric.closedBall 0 R := by
    intro t
    rw [Metric.mem_closedBall, dist_zero_right]
                                                        
    change norm (r * Complex.exp (I * t)) ≤ R
    rw [lem_modulus_of_ae_it hr_pos]
    exact le_of_lt hr_lt_R

  have hcomp_on : ContinuousOn (fun t : ℝ => f (r * Complex.exp (I * t))) Set.univ := by
    apply ContinuousOn.comp hf_cont (Continuous.continuousOn hparam_cont)
    intro t _
    exact hparam_range t

  exact continuousOn_univ.mp hcomp_on

lemma continuous_denominator_parameterized (r : ℝ) (z : ℂ) : Continuous (fun t : ℝ => (r * Complex.exp (I * t) - z) ^ 2) := by

  have h1 : Continuous (fun t : ℝ => r * Complex.exp (I * t) - z) := by
                                                         
    apply Continuous.sub
    ·                                                                                 
      exact continuous_real_parameterization r
    ·                                           
      exact continuous_const

  have h2 : Continuous (fun x : ℂ => x ^ 2) := continuous_pow 2

  exact Continuous.comp h2 h1

lemma interval_integrable_cauchy_integrand {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} {z : ℂ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hz : z ∈ Metric.closedBall 0 r_z) :
IntervalIntegrable (fun t => norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) MeasureTheory.volume 0 (2 * Real.pi) := by
                                                             
  apply Continuous.intervalIntegrable

  apply Continuous.comp continuous_norm

  apply Continuous.div₀

  · apply Continuous.mul
                                                     
    · exact continuous_real_parameterization r_int
                                                         
    · have h_r_int_pos : 0 < r_int := lt_trans h_r_z_pos h_r_z_lt_r_int
      exact continuous_f_parameterized hf_domain h_r_int_pos h_r_int_lt_R_analytic

  · exact continuous_denominator_parameterized r_int z

  · intro t
    exact lem_reverse_triangle6 t h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz

lemma integral_const_over_interval (C : ℝ) :
∫ _t in Set.Icc 0 (2 * Real.pi), C = (2 * Real.pi) * C := by
                                                                             
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
                                                                                     
  have h_le : (0 : ℝ) ≤ 2 * Real.pi := by
    apply mul_nonneg
    · norm_num
    · exact Real.pi_pos.le
  rw [← intervalIntegral.integral_of_le h_le]
                                                 
  rw [intervalIntegral.integral_const]
                                                        
  simp [sub_zero, smul_eq_mul]

lemma lem_calc_R_minus_r_prime {r R : ℝ}
    (_h_r_pos : 0 < r)
    (_h_r_lt_R : r < R) :
R - ((r + R) / 2) = (R - r) / 2 := by
  field_simp <;> ring

lemma lem_calc_denominator_specific {r R : ℝ}
    (h_r_pos : 0 < r)
    (h_r_lt_R : r < R) :
(R - ((r + R) / 2)) * (((r + R) / 2) - r) ^ 2 = ((R - r) ^ 3) / 8 := by
                                                           
  rw [lem_calc_R_minus_r_prime h_r_pos h_r_lt_R]
                                              
  have h_calc : ((r + R) / 2) - r = (R - r) / 2 := by
    field_simp <;> ring
                                
  rw [h_calc]

  ring

lemma lem_calc_numerator_specific {M r R : ℝ}
    (_hM_pos : 0 < M)
    (_hr_pos : 0 < r)
    (_hr_lt_R : r < R) :
2 * (((r + R) / 2) ^ 2) * M = ((R + r) ^ 2 * M) / 2 := by
                                                  
  ring

lemma lem_frac_simplify {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
    let r_prime := (r + R) / 2
(2 * (r_prime ^ 2) * M) / ((R - r_prime) * (r_prime - r) ^ 2) = (((R + r) ^ 2 * M) / 2) / (((R - r) ^ 3) / 8) := by
                                     
  dsimp only
                              
  have h_num := lem_calc_numerator_specific hM_pos hr_pos hr_lt_R
                                
  have h_denom := lem_calc_denominator_specific hr_pos hr_lt_R
                              
  rw [← h_num, ← h_denom]

lemma lem_frac_simplify2 {M r R : ℝ}
    (hM_pos : 0 < M)
    (_hr_pos : 0 < r)
    (hr_lt_R : r < R) :
((R + r) ^ 2 * M / 2) / ((R - r) ^ 3 / 8) = (4 * (R + r) ^ 2 * M) / ((R - r) ^ 3) := by

  have h_two_ne_zero : (2 : ℝ) ≠ 0 := by norm_num
  have h_eight_ne_zero : (8 : ℝ) ≠ 0 := by norm_num
  have h_R_minus_r_ne_zero : R - r ≠ 0 := by linarith [hr_lt_R]
  have h_R_minus_r_pow_ne_zero : (R - r) ^ 3 ≠ 0 := by
    apply pow_ne_zero
    exact h_R_minus_r_ne_zero

  field_simp [h_two_ne_zero, h_eight_ne_zero, h_R_minus_r_pow_ne_zero] <;> ring

lemma lem_frac_simplify3 {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
    let r_prime := (r + R) / 2
(2 * (r_prime ^ 2) * M) / ((R - r_prime) * (r_prime - r) ^ 2) = (4 * (R + r) ^ 2 * M) / ((R - r) ^ 3) := by
                              
  dsimp only
                                                         
  have h1 := lem_frac_simplify hM_pos hr_pos hr_lt_R
                                                            
  have h2 := lem_frac_simplify2 hM_pos hr_pos hr_lt_R
                          
  rw [h1, h2]

lemma lem_ineq_R_plus_r_lt_2R {r R : ℝ} (h_r_lt_R : r < R) :
R + r < 2 * R := by
                           
  rw [two_mul]
                                                                
  linarith [h_r_lt_R]

lemma lem_R_plus_r_is_positive {r R : ℝ}
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
0 < R + r := by
                                         
  have hR_pos : 0 < R := lt_trans hr_pos hr_lt_R
                                       
  exact add_pos hR_pos hr_pos

lemma lem_square_inequality_strict {a b : ℝ}
    (h_a_pos : 0 < a)
    (h_a_lt_b : a < b) :
a ^ 2 < b ^ 2 := by
                             
  have h_a_nonneg : 0 ≤ a := le_of_lt h_a_pos
                                                    
  have h_b_pos : 0 < b := lt_trans h_a_pos h_a_lt_b
  have h_b_nonneg : 0 ≤ b := le_of_lt h_b_pos
                                   
  have h_squares := mul_self_lt_mul_self_iff h_a_nonneg h_b_nonneg
                                                     
  have h_mult : a * a < b * b := h_squares.mp h_a_lt_b
                                                   
  rw [← pow_two, ← pow_two] at h_mult
  exact h_mult

lemma lem_2R_sq_is_4R_sq {R : ℝ} (_hR_pos : 0 < R) : (2 * R) ^ 2 = 4 * R ^ 2 := by
                                                  
  ring

lemma lem_ineq_R_plus_r_sq {r R : ℝ}
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
(R + r) ^ 2 < 4 * R ^ 2 := by
                      
  have h1 := lem_ineq_R_plus_r_lt_2R hr_lt_R
                  
  have h2 := lem_R_plus_r_is_positive hr_pos hr_lt_R
                                                                    
  have h3 := lem_square_inequality_strict h2 h1
                                                          
  have hR_pos : 0 < R := lt_trans hr_pos hr_lt_R
  have h4 := lem_2R_sq_is_4R_sq hR_pos
  rw [h4] at h3
  exact h3

lemma lem_ineq_R_plus_r_sqM {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
4 * (R + r) ^ 2 * M < 16 * R ^ 2 * M := by
                                                              
  have h_ineq := lem_ineq_R_plus_r_sq hr_pos hr_lt_R
                        
  have h_4M_pos : 0 < 4 * M := by
    apply mul_pos
    · norm_num
    · exact hM_pos
                                 
  have h_mult := mul_lt_mul_of_pos_right h_ineq h_4M_pos
                                      
  nlinarith [h_mult]

lemma lem_simplify_final_bound {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
(4 * (R + r) ^ 2 * M) / ((R - r) ^ 3) < (16 * R ^ 2 * M) / ((R - r) ^ 3) := by
                                                                
  have h_num_ineq := lem_ineq_R_plus_r_sqM hM_pos hr_pos hr_lt_R
                            
  have h_denom_pos : 0 < (R - r) ^ 3 := by
    apply pow_pos
    linarith [hr_lt_R]
                                
  exact div_lt_div_of_pos_right h_num_ineq h_denom_pos

lemma lem_bound_after_substitution {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
    let r_prime := (r + R) / 2
(2 * (r_prime ^ 2) * M) / ((R - r_prime) * (r_prime - r) ^ 2) ≤ (16 * R ^ 2 * M) / ((R - r) ^ 3) := by
                           
  dsimp only
                                                      
  have h1 := lem_frac_simplify3 hM_pos hr_pos hr_lt_R
                                 
  dsimp only at h1
  rw [h1]
                                                            
  have h2 := lem_simplify_final_bound hM_pos hr_pos hr_lt_R
                                  
  exact le_of_lt h2

open _root_.Complex _root_.MeasureTheory _root_.intervalIntegral
open scoped Interval

noncomputable def If_taxicab
    {r1 R R0: ℝ}
    (_hr1_pos : 0 < r1) (_hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    (f : ℂ → ℂ)
    (_hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R)) :
    (Metric.closedBall (0 : ℂ) r1) → ℂ :=
  fun z =>
    (∫ t in (0 : ℝ)..z.1.re, f (t : ℂ))
    + Complex.I * (∫ τ in (0 : ℝ)..z.1.im, f ((z.1.re : ℂ) + Complex.I * τ))

lemma def_If_z_plus_h
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (_hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1) :
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
      = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..(z + h).im, f (( (z + h).re : ℂ) + Complex.I * τ)) := by
  rfl

lemma def_If_z
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1) :
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩
      = (∫ t in (0 : ℝ)..z.re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ)) := by
  rfl

lemma def_If_w
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (_hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (_hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
      = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ)) := by
  simp [If_taxicab]

lemma continuous_vertical_line (a : ℂ) :
  Continuous (fun τ : ℝ => ((a.re : ℂ) + Complex.I * (τ : ℂ))) := by
  have hconst : Continuous (fun _ : ℝ => (a.re : ℂ)) := continuous_const
  have hmul : Continuous (fun τ : ℝ => (Complex.I : ℂ) * (τ : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  convert (preTransparency := .instances) hconst.add hmul using 1
  all_goals try with_reducible_and_instances rfl

lemma norm_re_add_I_mul_le_norm (a : ℂ) {τ : ℝ} (hτ : |τ| ≤ |a.im|) :
  ‖((a.re : ℂ) + Complex.I * (τ : ℂ))‖ ≤ ‖a‖ := by
                                                                              
  set z1 : ℂ := ((a.re : ℂ) + Complex.I * (τ : ℂ)) with hz1
                                       
  have hsq_z1 : ‖z1‖ ^ 2 = z1.re ^ 2 + z1.im ^ 2 := by
    have hx : ‖z1‖ ^ 2 - z1.re ^ 2 = z1.im ^ 2 := Complex.sq_norm_sub_sq_re z1
    have hx' := congrArg (fun t : ℝ => t + z1.re ^ 2) hx
                                          
    have : ‖z1‖ ^ 2 = z1.im ^ 2 + z1.re ^ 2 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx'
    simpa [add_comm] using this
  have hsq_a : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by
    have hx : ‖a‖ ^ 2 - a.re ^ 2 = a.im ^ 2 := Complex.sq_norm_sub_sq_re a
    have hx' := congrArg (fun t : ℝ => t + a.re ^ 2) hx
    have : ‖a‖ ^ 2 = a.im ^ 2 + a.re ^ 2 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx'
    simpa [add_comm] using this
                             
  have hz1_re : z1.re = a.re := by
    simp [hz1, mul_comm]
  have hz1_im : z1.im = τ := by
    simp [hz1, mul_comm]
                                                  
  have hτ_sq : τ ^ 2 ≤ a.im ^ 2 := by
    simpa using (sq_le_sq.mpr hτ)
                    
  have hsq_le : ‖z1‖ ^ 2 ≤ ‖a‖ ^ 2 := by
    have : a.re ^ 2 + τ ^ 2 ≤ a.re ^ 2 + a.im ^ 2 := add_le_add_right hτ_sq _
    simpa [hsq_z1, hz1_re, hz1_im, hsq_a] using this
                               
  have hnonneg : 0 ≤ ‖a‖ := norm_nonneg _
  exact le_of_sq_le_sq hsq_le hnonneg

lemma closedBall_mono_center0 {r1 R : ℝ} (h : r1 ≤ R) :
  Metric.closedBall (0 : ℂ) r1 ⊆ Metric.closedBall (0 : ℂ) R := by
  intro z hz
  have hz' : dist z (0 : ℂ) ≤ r1 := (Metric.mem_closedBall.mp hz)
  exact Metric.mem_closedBall.mpr (le_trans hz' h)

lemma abs_le_abs_of_mem_uIcc_zero {b t : ℝ} (ht : t ∈ Set.uIcc (0 : ℝ) b) : |t| ≤ |b| := by
  classical
  by_cases hb : 0 ≤ b
  ·                                  
    have ht' : t ∈ Set.Icc (0 : ℝ) b := by
      simpa [Set.uIcc_of_le hb] using ht
    have ht0 : 0 ≤ t := ht'.1
    have htb : t ≤ b := ht'.2
    have htabs : |t| = t := abs_of_nonneg ht0
    have hbabs : |b| = b := abs_of_nonneg hb
    simpa [htabs, hbabs] using htb
  ·                                  
    have ht' : t ∈ Set.Icc b 0 := by
      simpa [Set.uIcc_of_not_le hb] using ht
    have hb_le : b ≤ 0 := le_trans ht'.1 ht'.2
    have ht_le0 : t ≤ 0 := ht'.2
    have hbabs : |b| = -b := abs_of_nonpos hb_le
    have htabs : |t| = -t := abs_of_nonpos ht_le0
    have hneg : -t ≤ -b := neg_le_neg ht'.1
    simpa [htabs, hbabs] using hneg

lemma vertical_intervalIntegrable_of_mem_ball
    {r1 R R0 : ℝ}
    (_hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {a : ℂ}
    (ha : a ∈ Metric.closedBall (0 : ℂ) r1) :
    IntervalIntegrable (fun τ : ℝ => f (((a.re : ℂ)) + Complex.I * τ)) volume (0 : ℝ) a.im := by
  classical
                                              
  have hf_cont : ContinuousOn f (Metric.closedBall (0 : ℂ) R) := hf.continuousOn
                                 
  let g : ℝ → ℂ := fun τ => ((a.re : ℂ) + Complex.I * (τ : ℂ))
                                                        
  have hg_cont : ContinuousOn g (Set.uIcc (0 : ℝ) a.im) := by
    simpa [g] using (continuous_vertical_line a).continuousOn
                                                                  
  have hg_maps : Set.MapsTo g (Set.uIcc (0 : ℝ) a.im) (Metric.closedBall (0 : ℂ) R) := by
    intro τ hτ
    have hτabs : |τ| ≤ |a.im| := abs_le_abs_of_mem_uIcc_zero hτ
    have hnorm_le_a : ‖g τ‖ ≤ ‖a‖ := by
      simpa [g] using norm_re_add_I_mul_le_norm a hτabs
    have ha_norm : ‖a‖ ≤ r1 := by
      have : dist a (0 : ℂ) ≤ r1 := (Metric.mem_closedBall.mp ha)
      simpa [dist_eq_norm] using this
    have hnorm_le_r1 : ‖g τ‖ ≤ r1 := le_trans hnorm_le_a ha_norm
    have hg_mem_r1 : g τ ∈ Metric.closedBall (0 : ℂ) r1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm_le_r1
    exact (closedBall_mono_center0 (le_of_lt hr1_lt_R)) hg_mem_r1
                                                                          
  have hcomp : ContinuousOn (fun τ : ℝ => f (g τ)) (Set.uIcc (0 : ℝ) a.im) := by
                                                      
    convert (preTransparency := .instances) (ContinuousOn.comp (hg := hf_cont) (hf := hg_cont) (h := hg_maps)) using 1; rfl
                                                           
  have hInt : IntervalIntegrable (fun τ : ℝ => f (g τ)) volume (0 : ℝ) a.im :=
    ContinuousOn.intervalIntegrable (u := fun τ : ℝ => f (g τ)) (a := 0) (b := a.im) hcomp
  simpa [g] using hInt

lemma helper_im_of_w (z h : ℂ) : (((((z + h).re : ℂ) + Complex.I * z.im)).im) = z.im := by
  simp [Complex.add_im]

lemma helper_mul_sub_complex (x y : ℂ) : Complex.I * x - Complex.I * y = Complex.I * (x - y) := by
  simp [mul_sub]

lemma helper_re_of_w (z h : ℂ) : (((((z + h).re : ℂ) + Complex.I * z.im)).re) = (z + h).re := by
  simp

lemma diff_If_zh_w
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
      - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
      = Complex.I * (∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ)) := by
  classical
  intro w
                              
  let g : ℝ → ℂ := fun τ => f (((z + h).re : ℂ) + Complex.I * τ)
                                                              
  have hInt1 : IntervalIntegrable g volume (0 : ℝ) ((z + h).im) := by
    simpa [g] using
      (vertical_intervalIntegrable_of_mem_ball hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf (a := z + h) hzh)
  have hInt2 : IntervalIntegrable g volume (0 : ℝ) (z.im) := by
    have hInt2' :
        IntervalIntegrable
          (fun τ : ℝ => f (((( (((z + h).re : ℂ) + Complex.I * z.im)).re : ℂ)) + Complex.I * τ))
          volume (0 : ℝ) (((((z + h).re : ℂ) + Complex.I * z.im)).im) :=
      vertical_intervalIntegrable_of_mem_ball hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf
        (a := (((z + h).re : ℂ) + Complex.I * z.im)) hw
    simpa [g, helper_re_of_w z h, helper_im_of_w z h] using hInt2'
  have hinterval :
      ((∫ τ in (0 : ℝ)..(z + h).im, g τ) - ∫ τ in (0 : ℝ)..z.im, g τ)
      = ∫ τ in z.im..(z + h).im, g τ :=
    intervalIntegral.integral_interval_sub_left (μ := volume) (f := g) hInt1 hInt2
                                          
  have h1 :
      If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
        = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
          + Complex.I * (∫ τ in (0 : ℝ)..(z + h).im, g τ) := by
    have hzph := def_If_z_plus_h hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf (z := z) (h := h) hz hzh
    simpa [g] using hzph
  have h2 :
      If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
        = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
          + Complex.I * (∫ τ in (0 : ℝ)..z.im, g τ) := by
    have hwdef := def_If_w hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw
    simpa [g, w] using hwdef
                                                           
  calc
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
        - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
        = ((∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
            + Complex.I * (∫ τ in (0 : ℝ)..(z + h).im, g τ))
          - ((∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
            + Complex.I * (∫ τ in (0 : ℝ)..z.im, g τ)) := by
      simp [h1, h2]
    _ = (Complex.I * (∫ τ in (0 : ℝ)..(z + h).im, g τ))
          - (Complex.I * (∫ τ in (0 : ℝ)..z.im, g τ)) := by
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    _ = Complex.I *
          ((∫ τ in (0 : ℝ)..(z + h).im, g τ)
            - (∫ τ in (0 : ℝ)..z.im, g τ)) := by
      simp [helper_mul_sub_complex]
    _ = Complex.I * (∫ τ in z.im..(z + h).im, g τ) := by
      simpa using congrArg (fun t => Complex.I * t) hinterval
    _ = Complex.I * (∫ τ in z.im..(z + h).im,
          f (((z + h).re : ℂ) + Complex.I * τ)) := by
      simp [g]

lemma diff_If_w_z_initial_form
  {r1 R R0 : ℝ}
  (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ}
  (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  {z h : ℂ}
  (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
  (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
  (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
  let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
  (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩ - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    = (∫ t in z.re..w.re, f (t : ℂ))
      + Complex.I * (∫ τ in (0 : ℝ)..z.im, (f (w.re + Complex.I * τ) - f (z.re + Complex.I * τ))) := by
  intro w

  rw [def_If_w hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw]
  rw [def_If_z hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz]

  have hw_re : w.re = (z + h).re := by simp [w]
  have hw_im : w.im = z.im := by simp [w]

  have step1 :
    ((∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ)))
      - ((∫ t in (0 : ℝ)..z.re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ)))
    = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ)) - (∫ t in (0 : ℝ)..z.re, f (t : ℂ))
      + Complex.I * ((∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ))
        - (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ))) := by ring
  rw [step1]

  have horizontal_integrable_zh : IntervalIntegrable (fun t : ℝ => f (t : ℂ)) volume (0 : ℝ) (z + h).re := by
                                                                          
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.comp hf.continuousOn Complex.continuous_ofReal.continuousOn
    intro t ht
    simp [Metric.mem_closedBall, dist_eq_norm, Complex.norm_real]
                                                                  
    have : ‖z + h‖ ≤ r1 := by simp [← dist_zero_right]; exact Metric.mem_closedBall.mp hzh
    have : |(z + h).re| ≤ ‖z + h‖ := Complex.abs_re_le_norm (z + h)
    have : |t| ≤ |(z + h).re| := abs_le_abs_of_mem_uIcc_zero ht
    linarith [le_of_lt hr1_lt_R]

  have horizontal_integrable_z : IntervalIntegrable (fun t : ℝ => f (t : ℂ)) volume (0 : ℝ) z.re := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.comp hf.continuousOn Complex.continuous_ofReal.continuousOn
    intro t ht
    simp [Metric.mem_closedBall, dist_eq_norm, Complex.norm_real]
    have : ‖z‖ ≤ r1 := by simp [← dist_zero_right]; exact Metric.mem_closedBall.mp hz
    have : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have : |t| ≤ |z.re| := abs_le_abs_of_mem_uIcc_zero ht
    linarith [le_of_lt hr1_lt_R]

  have horizontal_eq :
    (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ)) - (∫ t in (0 : ℝ)..z.re, f (t : ℂ))
    = ∫ t in z.re..(z + h).re, f (t : ℂ) := by
    rw [← intervalIntegral.integral_interval_sub_left horizontal_integrable_zh horizontal_integrable_z]

  have vertical_integrable_zh : IntervalIntegrable (fun τ : ℝ => f (((z + h).re : ℂ) + Complex.I * τ)) volume (0 : ℝ) z.im := by
                                                     
    rw [← hw_re, ← hw_im]
    exact vertical_intervalIntegrable_of_mem_ball hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hw

  have vertical_integrable_z : IntervalIntegrable (fun τ : ℝ => f ((z.re : ℂ) + Complex.I * τ)) volume (0 : ℝ) z.im :=
    vertical_intervalIntegrable_of_mem_ball hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz

  have vertical_eq :
    (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ))
      - (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ))
    = ∫ τ in (0 : ℝ)..z.im, (f (((z + h).re : ℂ) + Complex.I * τ) - f ((z.re : ℂ) + Complex.I * τ)) := by
    rw [← intervalIntegral.integral_sub vertical_integrable_zh vertical_integrable_z]

  rw [horizontal_eq, vertical_eq, hw_re]

lemma algebraic_rearrangement_four_terms (a b c d : ℂ) :
    a - b + c - d = 0 → c - d = b - a := by
  intro h

  calc c - d
    = (a - b + c - d) - (a - b) := by ring
    _ = 0 - (a - b) := by rw [h]
    _ = -(a - b) := by ring
    _ = b - a := by ring

lemma real_between_as_convex_combination (b₁ b₂ t : ℝ)
  (h : (b₁ ≤ t ∧ t ≤ b₂) ∨ (b₂ ≤ t ∧ t ≤ b₁)) :
  ∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧ t = (1 - lam) * b₁ + lam * b₂ := by
                                                        
  cases' le_total b₁ b₂ with h₁ h₂
  case inl =>

    have ht : b₁ ≤ t ∧ t ≤ b₂ := by
      cases' h with h_left h_right
      · exact h_left
      ·                                                                           
        exact ⟨le_trans h₁ h_right.1, le_trans h_right.2 h₁⟩

    by_cases heq : b₁ = b₂
    ·                                              
      use 0
      constructor
      · norm_num
      constructor
      · norm_num
      · rw [heq] at ht ⊢
        have : t = b₂ := le_antisymm ht.2 ht.1
        rw [this]
        ring
    ·                            
      have hlt : b₁ < b₂ := lt_of_le_of_ne h₁ heq
      let lam := (t - b₁) / (b₂ - b₁)
      use lam
      constructor
      ·           
        apply div_nonneg
        · linarith [ht.1]
        · linarith [hlt]
      constructor
      ·                              
        rw [div_le_iff₀]
        · linarith [ht.2]                                         
        · linarith [hlt]                 
      ·                                 
        unfold lam
        have h_nonzero : b₂ - b₁ ≠ 0 := ne_of_gt (sub_pos.2 hlt)
        field_simp [h_nonzero] <;> ring
  case inr =>

    have ht : b₂ ≤ t ∧ t ≤ b₁ := by
      cases' h with h_left h_right
      ·                                                                           
        exact ⟨le_trans h₂ h_left.1, le_trans h_left.2 h₂⟩
      · exact h_right

    by_cases heq : b₁ = b₂
    ·                                              
      use 0
      constructor
      · norm_num
      constructor
      · norm_num
      · rw [← heq] at ht ⊢
        have : t = b₁ := le_antisymm ht.2 ht.1
        rw [this, heq]
        ring
    ·                            
      have hlt : b₂ < b₁ := lt_of_le_of_ne h₂ (Ne.symm heq)
      let lam := (b₁ - t) / (b₁ - b₂)
      use lam
      constructor
      ·           
        apply div_nonneg
        · linarith [ht.2]                           
        · linarith [hlt]                 
      constructor
      ·                              
        rw [div_le_iff₀]
        · linarith [ht.1]                                         
        · linarith [hlt]                 
      ·                                 
        unfold lam
        have h_nonzero : b₁ - b₂ ≠ 0 := ne_of_gt (sub_pos.2 hlt)
        field_simp [h_nonzero] <;> ring

lemma convex_combination_mem_segment {E : Type*} [AddCommGroup E] [Module ℝ E] (x y : E) (t : ℝ)
  (h₀ : 0 ≤ t) (h₁ : t ≤ 1) :
  (1 - t) • x + t • y ∈ segment ℝ x y := by

  use (1 - t), t
  constructor
  ·             
    linarith [h₁]
  constructor
  ·         
    exact h₀
  constructor
  ·                   
    ring
  ·                                             
    rfl

lemma vertical_line_in_segment (a : ℂ) (b₁ b₂ t : ℝ)
  (h : (b₁ ≤ t ∧ t ≤ b₂) ∨ (b₂ ≤ t ∧ t ≤ b₁)) :
  a + Complex.I * t ∈ segment ℝ (a + Complex.I * b₁) (a + Complex.I * b₂) := by
                                                
  obtain ⟨lam, h_lam_nonneg, h_lam_le_one, h_t_eq⟩ := real_between_as_convex_combination b₁ b₂ t h

  have h_convex : a + Complex.I * t = (1 - lam) • (a + Complex.I * b₁) + lam • (a + Complex.I * b₂) := by
                                           
    simp only [Complex.real_smul]
                                               
    rw [h_t_eq]
                                 
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
                                                                              
    rw [mul_add]
                                                      
    ring

  rw [h_convex]
  exact convex_combination_mem_segment (a + Complex.I * b₁) (a + Complex.I * b₂) lam h_lam_nonneg h_lam_le_one

lemma horizontal_line_in_segment (a : ℝ) (b₁ b₂ t : ℝ)
  (h : (b₁ ≤ t ∧ t ≤ b₂) ∨ (b₂ ≤ t ∧ t ≤ b₁)) :
  (t : ℂ) + Complex.I * a ∈ segment ℝ ((b₁ : ℂ) + Complex.I * a) ((b₂ : ℂ) + Complex.I * a) := by
                                                     
  obtain ⟨lam, h_lam_nonneg, h_lam_le_one, h_t_eq⟩ := real_between_as_convex_combination b₁ b₂ t h
                                                                        
  have h_convex : (t : ℂ) + Complex.I * a
      = (1 - lam) • ((b₁ : ℂ) + Complex.I * a) + lam • ((b₂ : ℂ) + Complex.I * a) := by
    simp only [Complex.real_smul]
                   
    rw [h_t_eq]
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
                                       
  simpa [h_convex] using
    (convex_combination_mem_segment ((b₁ : ℂ) + Complex.I * a) ((b₂ : ℂ) + Complex.I * a) lam h_lam_nonneg h_lam_le_one)

lemma intervalIntegrable_of_continuousOn_range (f : ℂ → ℂ) (g : ℝ → ℂ) (a b : ℝ) (S : Set ℂ)
  (hf : ContinuousOn f S) (hg : Continuous g)
  (hrange : ∀ t ∈ Set.uIcc a b, g t ∈ S) :
  IntervalIntegrable (f ∘ g) volume a b := by
                                                           
  have h_comp : ContinuousOn (f ∘ g) (Set.uIcc a b) := by
    apply ContinuousOn.comp hf (hg.continuousOn) hrange
                                                                     
  exact h_comp.intervalIntegrable

lemma intervalIntegrable_of_analyticOnNhd_of_endpoints_in_smaller_ball
  {r1 R : ℝ} (hr1_lt_R : r1 < R) {f : ℂ → ℂ}
  (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  {a : ℂ} {b₁ b₂ : ℝ}
  (h₁ : ‖a + Complex.I * b₁‖ ≤ r1) (h₂ : ‖a + Complex.I * b₂‖ ≤ r1) :
  IntervalIntegrable (fun t => f (a + Complex.I * t)) volume b₁ b₂ := by
                                                                    
  apply intervalIntegrable_of_continuousOn_range f (fun t => a + Complex.I * ↑t) b₁ b₂ (Metric.closedBall (0 : ℂ) R)
  ·                                                                              
    exact AnalyticOnNhd.continuousOn hf
  ·                                               
    exact Continuous.add continuous_const (Continuous.mul continuous_const continuous_ofReal)
  ·                                                         
    intro t ht
                                                                       
    have h_in_r1 : ‖a + Complex.I * ↑t‖ ≤ r1 := by
                                                            
      have h_segment : a + Complex.I * ↑t ∈ segment ℝ (a + Complex.I * b₁) (a + Complex.I * b₂) := by
        apply vertical_line_in_segment
        exact Set.mem_uIcc.mp ht
                                                              
      have h₁_mem : a + Complex.I * b₁ ∈ Metric.closedBall (0 : ℂ) r1 := by
        rwa [Metric.mem_closedBall, dist_zero_right]
      have h₂_mem : a + Complex.I * b₂ ∈ Metric.closedBall (0 : ℂ) r1 := by
        rwa [Metric.mem_closedBall, dist_zero_right]
                                         
      have h_subset := (convex_closedBall (0 : ℂ) r1).segment_subset h₁_mem h₂_mem
      have h_in_ball := h_subset h_segment
      rwa [Metric.mem_closedBall, dist_zero_right] at h_in_ball
                                                              
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_trans h_in_r1 (le_of_lt hr1_lt_R)

lemma cauchy_for_rectangles
    {r1 R R0 : ℝ}
    (_hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z w : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : w ∈ Metric.closedBall (0 : ℂ) r1)
    (hzw : ((w.re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1)
    (hwz : ((z.re : ℂ) + Complex.I * w.im) ∈ Metric.closedBall (0 : ℂ) r1) :
    (∫ x in z.re..w.re, f ((x : ℂ) + Complex.I * (z.im)))
    - (∫ x in z.re..w.re, f ((x : ℂ) + Complex.I * (w.im)))
    + Complex.I * (∫ y in z.im..w.im, f ((w.re : ℂ) + Complex.I * y))
    - Complex.I * (∫ y in z.im..w.im, f ((z.re : ℂ) + Complex.I * y)) = 0 := by
  classical
                                                                                    
  have hA : ((z.re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
                          
    have hz_eq : z = (z.re : ℂ) + Complex.I * z.im := by
      exact (lem_wReIm z)
    rwa [← hz_eq]
  have hC : ((w.re : ℂ) + Complex.I * w.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
                          
    have hw_eq : w = (w.re : ℂ) + Complex.I * w.im := by
      exact (lem_wReIm w)
    rwa [← hw_eq]
                                                                                                
  have h_left_in_ball : ∀ y ∈ Set.uIcc z.im w.im,
      ((z.re : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := by
    intro y hy
    have hseg : (z.re : ℂ) + Complex.I * (y : ℂ)
        ∈ segment ℝ ((z.re : ℂ) + Complex.I * z.im) ((z.re : ℂ) + Complex.I * w.im) := by
      simpa using vertical_line_in_segment (a := (z.re : ℂ)) (b₁ := z.im) (b₂ := w.im) (t := y)
        (h := Set.mem_uIcc.mp hy)
    exact (convex_closedBall (0 : ℂ) r1).segment_subset hA hwz hseg
  have h_right_in_ball : ∀ y ∈ Set.uIcc z.im w.im,
      ((w.re : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := by
    intro y hy
    have hseg : (w.re : ℂ) + Complex.I * (y : ℂ)
        ∈ segment ℝ ((w.re : ℂ) + Complex.I * z.im) ((w.re : ℂ) + Complex.I * w.im) := by
      simpa using vertical_line_in_segment (a := (w.re : ℂ)) (b₁ := z.im) (b₂ := w.im) (t := y)
        (h := Set.mem_uIcc.mp hy)
    exact (convex_closedBall (0 : ℂ) r1).segment_subset hzw hC hseg
  have h_point_in_ball : ∀ x ∈ Set.uIcc z.re w.re, ∀ y ∈ Set.uIcc z.im w.im,
      ((x : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := by
    intro x hx y hy
    have hL : ((z.re : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := h_left_in_ball y hy
    have hR' : ((w.re : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := h_right_in_ball y hy
                                                                
    obtain ⟨lam, hlam0, hlam1, hx_eq⟩ := real_between_as_convex_combination z.re w.re x (Set.mem_uIcc.mp hx)
    have hseg_horiz : (x : ℂ) + Complex.I * (y : ℂ)
        ∈ segment ℝ ((z.re : ℂ) + Complex.I * (y : ℂ)) ((w.re : ℂ) + Complex.I * (y : ℂ)) := by
                                    
      have : (x : ℂ) + Complex.I * (y : ℂ)
          = (1 - lam) • ((z.re : ℂ) + Complex.I * (y : ℂ)) + lam • ((w.re : ℂ) + Complex.I * (y : ℂ)) := by
        simp only [Complex.real_smul]
                                                    
        rw [hx_eq]
        simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
        ring
      simpa [this] using
        (convex_combination_mem_segment ((z.re : ℂ) + Complex.I * (y : ℂ)) ((w.re : ℂ) + Complex.I * (y : ℂ)) lam hlam0 hlam1)
    exact (convex_closedBall (0 : ℂ) r1).segment_subset hL hR' hseg_horiz
                                                                
  set S := ([[z.re, w.re]] ×ℂ [[z.im, w.im]])
  have hS_subset_r1 : S ⊆ Metric.closedBall (0 : ℂ) r1 := by
    intro p hp
    have hx : p.re ∈ [[z.re, w.re]] := hp.1
    have hy : p.im ∈ [[z.im, w.im]] := hp.2
                                                              
    have : ((p.re : ℂ) + Complex.I * (p.im : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 :=
      h_point_in_ball p.re hx p.im hy
                                                                       
    have hp_eq : p = (p.re : ℂ) + Complex.I * (p.im : ℂ) := lem_wReIm p
    rwa [hp_eq]
  have hS_subset_R : S ⊆ Metric.closedBall (0 : ℂ) R :=
    fun p hp => (closedBall_mono_center0 (le_of_lt hr1_lt_R)) (hS_subset_r1 hp)
                                                                               
  have Hdiff : DifferentiableOn ℂ f S := by
    intro p hp
    have hpR : p ∈ Metric.closedBall (0 : ℂ) R := hS_subset_R hp
    exact (hf p hpR).differentiableAt.differentiableWithinAt
                                                          
  simpa [smul_eq_mul, mul_comm] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w Hdiff

lemma cauchy_for_horizontal_strip
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (∫ t in z.re..(z + h).re, f (t : ℂ))
    - (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im))
    + Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ))
    - Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ)) = 0 := by
                                                                               
  let z₀ : ℂ := (z.re : ℂ)
  let w₀ : ℂ := (z + h).re + Complex.I * z.im
                         
  have hz₀ : z₀ ∈ Metric.closedBall (0 : ℂ) r1 := by
    have hz_norm : ‖z‖ ≤ r1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hzre_le : ‖(z.re : ℂ)‖ ≤ ‖z‖ := by
      rw [Complex.norm_real]
      exact Complex.abs_re_le_norm z
    have : ‖z₀‖ ≤ r1 := le_trans hzre_le hz_norm
    simpa [z₀, Metric.mem_closedBall, dist_eq_norm] using this
  have hw₀ : w₀ ∈ Metric.closedBall (0 : ℂ) r1 := hw
                                                  
  have hzw : ((w₀.re : ℂ) + Complex.I * z₀.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
                                                          
    have h1 : ((w₀.re : ℂ) + Complex.I * z₀.im) = ((z + h).re : ℂ) := by
      simp [w₀, z₀, Complex.ofReal_im, mul_zero, add_zero]
    rw [h1]
    have h2 : ‖((z + h).re : ℂ)‖ ≤ ‖z + h‖ := by
      rw [Complex.norm_real]
      exact Complex.abs_re_le_norm (z + h)
    have h3 : ‖z + h‖ ≤ r1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hzh
    simpa [Metric.mem_closedBall, dist_eq_norm] using le_trans h2 h3
  have hwz : ((z₀.re : ℂ) + Complex.I * w₀.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
                                            
    have h1 : ((z₀.re : ℂ) + Complex.I * w₀.im) = z := by
      simp [z₀, w₀, Complex.ofReal_re]
      exact (lem_wReIm z).symm
    rw [h1]
    exact hz
                                   
  have H := cauchy_for_rectangles (r1:=r1) (R:=R) (R0:=R0) hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz₀ hw₀ hzw hwz

  rw [(show z₀.re = z.re by simp [z₀])] at H
  rw [(show z₀.im = (0 : ℝ) by simp [z₀])] at H
  rw [(show w₀.re = (z + h).re by simp [w₀])] at H
  rw [(show w₀.im = z.im by simp [w₀])] at H

  convert (preTransparency := .instances) H using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Complex.ofReal_zero, mul_zero, add_zero]

lemma integrability_from_cauchy_horizontal_strip
    {r1 R R0 : ℝ} (_hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) r1) (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    IntervalIntegrable (fun τ => f (((z + h).re : ℂ) + Complex.I * τ)) volume (0 : ℝ) z.im ∧
    IntervalIntegrable (fun τ => f ((z.re : ℂ) + Complex.I * τ)) volume (0 : ℝ) z.im := by
  constructor
  ·                                                         
    apply intervalIntegrable_of_analyticOnNhd_of_endpoints_in_smaller_ball hr1_lt_R hf
    ·                                           
      simp only [Complex.ofReal_zero, mul_zero, add_zero, Complex.norm_real]
      rw [Metric.mem_closedBall, dist_zero_right] at hzh
      exact le_trans (Complex.abs_re_le_norm (z + h)) hzh
    ·                                              
      rw [Metric.mem_closedBall, dist_zero_right] at hw
      exact hw
  ·                                                    
    apply intervalIntegrable_of_analyticOnNhd_of_endpoints_in_smaller_ball hr1_lt_R hf
    ·                                     
      simp only [Complex.ofReal_zero, mul_zero, add_zero, Complex.norm_real]
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      exact le_trans (Complex.abs_re_le_norm z) hz
    ·                                        
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      rw [← lem_wReIm z]
      exact hz

lemma cauchy_rearrangement_step1
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    Complex.I * (∫ τ in (0 : ℝ)..z.im, (f (((z + h).re : ℂ) + Complex.I * τ) - f ((z.re : ℂ) + Complex.I * τ)))
      = (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im)) - (∫ t in z.re..(z + h).re, f (t : ℂ)) := by
                                   
  have H := cauchy_for_horizontal_strip hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  have integrable := integrability_from_cauchy_horizontal_strip hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  have rearrange := algebraic_rearrangement_four_terms
    (∫ t in z.re..(z + h).re, f (t : ℂ))
    (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im))
    (Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ)))
    (Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ)))
    H

  have vertical_linearity :
    Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ))
    - Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ))
    = Complex.I * (∫ τ in (0 : ℝ)..z.im, (f (((z + h).re : ℂ) + Complex.I * τ) - f ((z.re : ℂ) + Complex.I * τ))) := by
    rw [← mul_sub]
    rw [← intervalIntegral.integral_sub integrable.1 integrable.2]

  rw [← vertical_linearity]
  exact rearrange

lemma diff_If_w_z
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
      - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩
      = (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im)) := by

  have initial_form := diff_If_w_z_initial_form hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  have rearrange_step := cauchy_rearrangement_step1 hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  have w_re_eq : (((z + h).re : ℂ) + Complex.I * z.im).re = (z + h).re := by
    simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]

  simp_rw [initial_form, w_re_eq, rearrange_step]

  ring

lemma If_difference_is_L_path_integral
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    = (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im))
      + Complex.I * (∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ)) := by

  let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im

  calc If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
       - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩
     = (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
        - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩)
       + (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
          - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩) := by ring
     _ = Complex.I * (∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ))
       + (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im)) := by
       rw [diff_If_zh_w hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw,
           diff_If_w_z hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw]
     _ = (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im))
       + Complex.I * (∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ)) := by ring

lemma If_diff_add_sub_identity
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    =
    (∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z) + f z)
    + Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z) + f z) := by
                                                                                               
  have H :=
    If_difference_is_L_path_integral (hr1_pos) (hr1_lt_R) (hR_lt_R0) (hR0_lt_one) hf hz hzh hw
  simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using H

lemma intervalIntegrable_of_analyticOnNhd_of_horizontal_endpoints_in_smaller_ball
  {r1 R : ℝ} (hr1_lt_R : r1 < R) {f : ℂ → ℂ}
  (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  {im_part : ℝ} {a b : ℝ}
  (h₁ : ‖(a : ℂ) + Complex.I * im_part‖ ≤ r1) (h₂ : ‖(b : ℂ) + Complex.I * im_part‖ ≤ r1) :
  IntervalIntegrable (fun t => f ((t : ℂ) + Complex.I * im_part)) volume a b := by
                                                                    
  apply intervalIntegrable_of_continuousOn_range f (fun t => (t : ℂ) + Complex.I * im_part) a b (Metric.closedBall (0 : ℂ) R)
  ·                                                                              
    exact AnalyticOnNhd.continuousOn hf
  ·                                                                     
    exact Continuous.add continuous_ofReal continuous_const
  ·                                                         
    intro t ht
                                                                       
    have h_in_r1 : ‖(t : ℂ) + Complex.I * im_part‖ ≤ r1 := by
                                                            
      have h_segment : (t : ℂ) + Complex.I * im_part ∈ segment ℝ ((a : ℂ) + Complex.I * im_part) ((b : ℂ) + Complex.I * im_part) := by

        obtain ⟨lam, h_lam_nonneg, h_lam_le_one, h_t_eq⟩ := real_between_as_convex_combination a b t (Set.mem_uIcc.mp ht)

        have h_convex : (t : ℂ) + Complex.I * im_part = (1 - lam) • ((a : ℂ) + Complex.I * im_part) + lam • ((b : ℂ) + Complex.I * im_part) := by
                                                 
          simp only [Complex.real_smul]
                                                   
          rw [h_t_eq]
                                       
          simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
                                             
          ring

        rw [h_convex]
        exact convex_combination_mem_segment ((a : ℂ) + Complex.I * im_part) ((b : ℂ) + Complex.I * im_part) lam h_lam_nonneg h_lam_le_one

      have h₁_mem : (a : ℂ) + Complex.I * im_part ∈ Metric.closedBall (0 : ℂ) r1 := by
        rwa [Metric.mem_closedBall, dist_zero_right]
      have h₂_mem : (b : ℂ) + Complex.I * im_part ∈ Metric.closedBall (0 : ℂ) r1 := by
        rwa [Metric.mem_closedBall, dist_zero_right]
                                         
      have h_subset := (convex_closedBall (0 : ℂ) r1).segment_subset h₁_mem h₂_mem
      have h_in_ball := h_subset h_segment
      rwa [Metric.mem_closedBall, dist_zero_right] at h_in_ball
                                                              
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_trans h_in_r1 (le_of_lt hr1_lt_R)

lemma If_diff_linearity
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    =
    ((∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z))
     + (∫ _t in z.re..(z + h).re, f z))
    + Complex.I *
      ((∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))
       + (∫ _τ in z.im..(z + h).im, f z)) := by
                                                                                             
  have H := If_diff_add_sub_identity hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  have hz_norm : ‖z‖ ≤ r1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hz
  have hzh_norm : ‖z + h‖ ≤ r1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hzh
  have hw_norm : ‖((z + h).re : ℂ) + Complex.I * z.im‖ ≤ r1 := by
    rwa [Metric.mem_closedBall, dist_zero_right] at hw

  have h_z_eq : z = (z.re : ℂ) + Complex.I * z.im := lem_wReIm z
  have h_zh_eq : z + h = ((z + h).re : ℂ) + Complex.I * (z + h).im := lem_wReIm (z + h)

  have hz_endpoint : ‖(z.re : ℂ) + Complex.I * z.im‖ ≤ r1 := by rwa [← h_z_eq]
  have h_horiz_integrable := intervalIntegrable_of_analyticOnNhd_of_horizontal_endpoints_in_smaller_ball
    hr1_lt_R hf hz_endpoint hw_norm

  have hzh_endpoint : ‖((z + h).re : ℂ) + Complex.I * (z + h).im‖ ≤ r1 := by rwa [← h_zh_eq]
  have h_vert_integrable := intervalIntegrable_of_analyticOnNhd_of_endpoints_in_smaller_ball
    hr1_lt_R hf hw_norm hzh_endpoint

  have h_const_horiz : IntervalIntegrable (fun _ => f z) volume z.re (z + h).re := intervalIntegrable_const
  have h_const_vert : IntervalIntegrable (fun _ => f z) volume z.im (z + h).im := intervalIntegrable_const

  have h_diff_horiz : IntervalIntegrable (fun t => f (t + Complex.I * z.im) - f z) volume z.re (z + h).re :=
    IntervalIntegrable.sub h_horiz_integrable h_const_horiz

  have h_diff_vert : IntervalIntegrable (fun τ => f (((z + h).re : ℂ) + Complex.I * τ) - f z) volume z.im (z + h).im :=
    IntervalIntegrable.sub h_vert_integrable h_const_vert

  have h1 : ∫ t in z.re..(z + h).re, ((f (t + Complex.I * z.im) - f z) + f z) =
           (∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)) + (∫ t in z.re..(z + h).re, f z) :=
    intervalIntegral.integral_add h_diff_horiz h_const_horiz

  have h2 : ∫ τ in z.im..(z + h).im, ((f (((z + h).re : ℂ) + Complex.I * τ) - f z) + f z) =
           (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)) + (∫ τ in z.im..(z + h).im, f z) :=
    intervalIntegral.integral_add h_diff_vert h_const_vert

  rw [H, h1, h2, mul_add]

lemma integral_of_constant_over_L_path
    {r1 R R0 : ℝ}
    (_hr1_pos : 0 < r1) (_hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (_hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (_hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (_hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1) :
    (∫ _t in z.re..(z + h).re, f z) + Complex.I * (∫ _τ in z.im..(z + h).im, f z)
      = f z * h := by
                                                           
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const]

  rw [Complex.add_re, Complex.add_im]
  simp only [add_sub_cancel_left]

  rw [Complex.real_smul, Complex.real_smul]

  rw [← mul_assoc]

  rw [← add_mul]

  rw [mul_comm Complex.I (↑h.im)]

  rw [Complex.re_add_im h]

  rw [mul_comm]

noncomputable def Err
    {r1 R R0 : ℝ}
    (_hr1_pos : 0 < r1) (_hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    (f : ℂ → ℂ)
    (_hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    (z h : ℂ) : ℂ :=
  (∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z))
  + Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))

lemma If_diff_decomposition_final
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    = f z * h
      + Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h := by
                                                                                      
  have H :=
    If_diff_linearity (hr1_pos) (hr1_lt_R) (hR_lt_R0) (hR0_lt_one)
      (f := f) (hf := hf)
      (z := z) (h := h)
      (hz := hz) (hzh := hzh) (hw := hw)
                                                                   
  let A : ℂ := ∫ t in z.re..(z + h).re, f (t + Complex.I * z.im) - f z
  let B : ℂ := ∫ t in z.re..(z + h).re, f z
  let C : ℂ := ∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ) - f z
  let D : ℂ := ∫ τ in z.im..(z + h).im, f z
                                                                    
  have hH' : (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
     = (A + B) + Complex.I * (C + D) := by
    simpa [A, B, C, D, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using H
                                                                          
  have hsplit : (A + B) + Complex.I * (C + D)
      = (A + Complex.I * C) + (B + Complex.I * D) := by ring
  have hH'' : (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
     = (A + Complex.I * C) + (B + Complex.I * D) := by
    simpa [hsplit] using hH'
                                                               
  have hBD : (B + Complex.I * D) = f z * h := by
    simpa [B, D] using
      integral_of_constant_over_L_path (r1:=r1) (R:=R) (R0:=R0) hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh
  have hH''' : (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
     = (A + Complex.I * C) + f z * h := by
    simpa [hBD] using hH''
                                                                
  have hH4 : (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
     = Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h + f z * h := by
    simpa [Err, A, C, add_comm, add_left_comm, add_assoc] using hH'''
                                                         
  simpa [Err, add_comm, add_left_comm, add_assoc] using hH4

noncomputable def S_horiz (z h : ℂ) (f : ℂ → ℂ) : ℝ :=
  sSup {r | ∃ t ∈ Set.uIcc z.re (z + h).re,
        r = ‖f (t + Complex.I * z.im) - f z‖}

noncomputable def S_vert (z h : ℂ) (f : ℂ → ℂ) : ℝ :=
  sSup {r | ∃ τ ∈ Set.uIcc z.im (z + h).im,
        r = ‖f (((z + h).re : ℂ) + Complex.I * τ) - f z‖}

noncomputable def S_max (z h : ℂ) (f : ℂ → ℂ) : ℝ :=
  max (S_horiz z h f) (S_vert z h f)

lemma bound_on_Err
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
  (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
  (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
  ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h‖
      ≤ |h.re| * S_max z h f + |h.im| * S_max z h f := by
                                                          
  unfold Err
                                    
  have hsplit :
      ‖(∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z))
        + Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖
      ≤ ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
        + ‖Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖ :=
    norm_add_le _ _

  have hI : ‖Complex.I‖ = (1 : ℝ) := by simp
  have hvertnorm :
      ‖Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖
        = ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖ := by
    simp [hI, one_mul]

  set SH : Set ℝ := {r | ∃ t ∈ Set.uIcc z.re (z + h).re,
      r = ‖f (t + Complex.I * z.im) - f z‖}
  have hbdd_SH : BddAbove SH := by
    classical
                                                
    have hK : IsCompact (Set.uIcc z.re (z + h).re) := isCompact_uIcc
                                  
    let γ : ℝ → ℂ := fun t => (t : ℂ) + Complex.I * z.im
    have hγ_cont : Continuous γ := by
      convert (preTransparency := .instances) (Complex.continuous_ofReal.add (continuous_const (y := Complex.I * (z.im : ℂ)))) using 1
      all_goals try with_reducible_and_instances rfl
    have hz_mem : ((z.re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      rw [show (z.re : ℂ) + Complex.I * z.im = z.re + z.im * Complex.I by ring]
      rw [Complex.re_add_im]
      rwa [Metric.mem_closedBall, dist_zero_right] at hz
    have hw_mem : (((z + h).re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
      simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hw
    have hseg_subset :
        (γ '' Set.uIcc z.re (z + h).re) ⊆ Metric.closedBall (0 : ℂ) r1 := by
      intro w hwim
      rcases hwim with ⟨t, ht, rfl⟩
                                                                  
      have hseg : ((t : ℂ) + Complex.I * z.im)
          ∈ segment ℝ ((z.re : ℂ) + Complex.I * z.im)
                          (((z + h).re : ℂ) + Complex.I * z.im) := by

        have := horizontal_line_in_segment (a := z.im) (b₁ := z.re) (b₂ := (z + h).re)
          (t := t) (by simpa [Set.mem_uIcc] using ht)
        simpa using this
      have hz_in : ((z.re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := hz_mem
      have hw_in : (((z + h).re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := hw_mem
      have hsubset := (convex_closedBall (0 : ℂ) r1).segment_subset hz_in hw_in
      have hw' := hsubset hseg
      simpa [Metric.mem_closedBall, dist_zero_right] using hw'
    have hf_cont : ContinuousOn f (Metric.closedBall (0 : ℂ) R) := hf.continuousOn
                                                        
    have hmaps : Set.MapsTo γ (Set.uIcc z.re (z + h).re) (Metric.closedBall (0 : ℂ) R) := by
      intro t ht
      have himg_r1 : γ t ∈ Metric.closedBall (0 : ℂ) r1 := by
        exact hseg_subset (Set.mem_image_of_mem _ ht)
      exact (closedBall_mono_center0 (le_of_lt hr1_lt_R)) himg_r1
    have hcont_on : ContinuousOn (fun t => f (γ t)) (Set.uIcc z.re (z + h).re) := by
      convert (preTransparency := .instances) (ContinuousOn.comp (hf_cont) (hγ_cont.continuousOn) hmaps) using 1; rfl
                                                         
    have hψ : Continuous (fun w : ℂ => ‖w - f z‖) :=
      (continuous_id.sub continuous_const).norm
    have hR_cont : ContinuousOn (fun t => ‖f (γ t) - f z‖) (Set.uIcc z.re (z + h).re) := by
                                              
      have h_cont_sub : ContinuousOn (fun t => f (γ t) - f z) (Set.uIcc z.re (z + h).re) :=
        hcont_on.sub continuousOn_const
                        
      exact h_cont_sub.norm
                                            
    have himage_compact : IsCompact ((fun t => ‖f (γ t) - f z‖) '' Set.uIcc z.re (z + h).re) :=
      IsCompact.image_of_continuousOn hK hR_cont
                                    
    have hSH_eq : SH = (fun t => ‖f (γ t) - f z‖) '' Set.uIcc z.re (z + h).re := by
      ext r; constructor
      · intro hr; rcases hr with ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
      · intro hr; rcases hr with ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
                                           
    have : BddAbove ((fun t => ‖f (γ t) - f z‖) '' Set.uIcc z.re (z + h).re) :=
      himage_compact.bddAbove
    simpa [hSH_eq] using this

  set SV : Set ℝ := {r | ∃ τ ∈ Set.uIcc z.im (z + h).im,
      r = ‖f (((z + h).re : ℂ) + Complex.I * τ) - f z‖}
  have hbdd_SV : BddAbove SV := by
    classical
                                          
    have hK : IsCompact (Set.uIcc z.im (z + h).im) := isCompact_uIcc
    let γv : ℝ → ℂ := fun τ => ((z + h).re : ℂ) + Complex.I * τ
    have hγv_cont : Continuous γv := by
      have hmul : Continuous (fun τ : ℝ => Complex.I * (τ : ℂ)) := by
        exact continuous_const.mul Complex.continuous_ofReal
      simp only [γv]
      exact continuous_const.add hmul
    have hw_mem' : (((z + h).re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hw
    have hzh_mem : (((z + h).re : ℂ) + Complex.I * (z + h).im) ∈ Metric.closedBall (0 : ℂ) r1 := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      rw [show ((z + h).re : ℂ) + Complex.I * (z + h).im = (z + h).re + (z + h).im * Complex.I by ring]
      rw [Complex.re_add_im]
      rwa [Metric.mem_closedBall, dist_zero_right] at hzh
    have hseg_subset :
        (γv '' Set.uIcc z.im (z + h).im) ⊆ Metric.closedBall (0 : ℂ) r1 := by
      intro w hwim; rcases hwim with ⟨τ, hτ, rfl⟩
      have hseg : (((z + h).re : ℂ) + Complex.I * τ)
          ∈ segment ℝ (((z + h).re : ℂ) + Complex.I * z.im)
                          (((z + h).re : ℂ) + Complex.I * (z + h).im) := by
        have := vertical_line_in_segment (((z + h).re : ℂ)) (b₁ := z.im) (b₂ := (z + h).im) (t := τ)
          (by simpa [Set.mem_uIcc] using hτ)
        simpa using this
      have hz_in := hw_mem'
      have hw_in := hzh_mem
      have hsubset := (convex_closedBall (0 : ℂ) r1).segment_subset hz_in hw_in
      have hw' := hsubset hseg
      simp only [Metric.mem_closedBall, dist_zero_right] at hw'
      rwa [Metric.mem_closedBall, dist_zero_right]
    have hmaps : Set.MapsTo γv (Set.uIcc z.im (z + h).im) (Metric.closedBall (0 : ℂ) R) := by
      intro τ hτ; have : γv τ ∈ Metric.closedBall (0 : ℂ) r1 := hseg_subset (Set.mem_image_of_mem _ hτ)
      exact (closedBall_mono_center0 (le_of_lt hr1_lt_R)) this
    have hf_cont : ContinuousOn f (Metric.closedBall (0 : ℂ) R) := hf.continuousOn
    have hcont_on : ContinuousOn (fun τ => f (γv τ)) (Set.uIcc z.im (z + h).im) := by
      convert (preTransparency := .instances) (ContinuousOn.comp (hf_cont) (hγv_cont.continuousOn) hmaps) using 1; rfl
    have hψ : Continuous (fun w : ℂ => ‖w - f z‖) :=
      (continuous_id.sub continuous_const).norm
    have hR_cont : ContinuousOn (fun τ => ‖f (γv τ) - f z‖) (Set.uIcc z.im (z + h).im) := by
      have h1 : ContinuousOn (fun τ => f (γv τ) - f z) (Set.uIcc z.im (z + h).im) := by
        exact hcont_on.sub continuousOn_const
      exact h1.norm
    have himage_compact : IsCompact ((fun τ => ‖f (γv τ) - f z‖) '' Set.uIcc z.im (z + h).im) :=
      IsCompact.image_of_continuousOn hK hR_cont
    have hSV_eq : SV = (fun τ => ‖f (γv τ) - f z‖) '' Set.uIcc z.im (z + h).im := by
      ext r; constructor
      · intro hr; rcases hr with ⟨τ, hτ, rfl⟩; exact ⟨τ, hτ, rfl⟩
      · intro hr; rcases hr with ⟨τ, hτ, rfl⟩; exact ⟨τ, hτ, rfl⟩
    have : BddAbove ((fun τ => ‖f (γv τ) - f z‖) '' Set.uIcc z.im (z + h).im) :=
      himage_compact.bddAbove
    simpa [hSV_eq] using this

  have hC_horiz : ∀ t ∈ Set.uIcc z.re (z + h).re,
      ‖(f (t + Complex.I * z.im) - f z)‖ ≤ S_horiz z h f := by
    intro t ht
    have hx : ‖f (t + Complex.I * z.im) - f z‖ ∈ SH := ⟨t, ht, rfl⟩
                                              
    have : S_horiz z h f = sSup SH := rfl
    simpa [this] using (le_csSup hbdd_SH hx)

  have hC_vert : ∀ τ ∈ Set.uIcc z.im (z + h).im,
      ‖(f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖ ≤ S_vert z h f := by
    intro τ hτ
    have hx : ‖f (((z + h).re : ℂ) + Complex.I * τ) - f z‖ ∈ SV := ⟨τ, hτ, rfl⟩
    have : S_vert z h f = sSup SV := rfl
    simpa [this] using (le_csSup hbdd_SV hx)

  have hH : ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
            ≤ |(z + h).re - z.re| * S_horiz z h f := by
                                           
    have h_bound : ∀ t, t ∈ [[z.re, (z + h).re]] → ‖f (↑t + Complex.I * ↑z.im) - f z‖ ≤ S_horiz z h f := by
      intro t ht; exact hC_horiz t ht
    have h_int : ∀ t ∈ Ι z.re (z + h).re, ‖f (↑t + Complex.I * ↑z.im) - f z‖ ≤ S_horiz z h f := by
      intro t ht
      have ht_uIcc : t ∈ Set.uIcc z.re (z + h).re := by
                                             
        exact Set.uIoc_subset_uIcc ht
      exact h_bound t ht_uIcc
    have := intervalIntegral.norm_integral_le_of_norm_le_const h_int
    convert (preTransparency := .instances) this using 1
    all_goals try with_reducible_and_instances rfl
    ring

  have hV : ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖
            ≤ |(z + h).im - z.im| * S_vert z h f := by
    have h_bound : ∀ τ, τ ∈ [[z.im, (z + h).im]] → ‖f (↑(z + h).re + Complex.I * ↑τ) - f z‖ ≤ S_vert z h f := by
      intro τ hτ; exact hC_vert τ hτ
    have h_int : ∀ τ ∈ Ι z.im (z + h).im, ‖f (↑(z + h).re + Complex.I * ↑τ) - f z‖ ≤ S_vert z h f := by
      intro τ hτ
      have hτ_uIcc : τ ∈ Set.uIcc z.im (z + h).im := by
                                             
        exact Set.uIoc_subset_uIcc hτ
      exact h_bound τ hτ_uIcc
    have := intervalIntegral.norm_integral_le_of_norm_le_const h_int
    rwa [mul_comm] at this

  have hre' : (z + h).re - z.re = h.re := by
    simp [Complex.add_re]
  have him' : (z + h).im - z.im = h.im := by
    simp [Complex.add_im]
  have hre : |(z + h).re - z.re| = |h.re| := by simp
  have him : |(z + h).im - z.im| = |h.im| := by simp

  have hH' : ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
                ≤ |h.re| * S_max z h f := by
    have : S_horiz z h f ≤ S_max z h f := by exact le_max_left _ _
                                 
    have hH_rewritten : ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖ ≤ |h.re| * S_horiz z h f := by
      rwa [hre] at hH
                           
    have h_bound := mul_le_mul_of_nonneg_left this (abs_nonneg (h.re))
    exact le_trans hH_rewritten h_bound

  have hV' : ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖
                ≤ |h.im| * S_max z h f := by
    have : S_vert z h f ≤ S_max z h f := by exact le_max_right _ _
                                 
    have hV_rewritten : ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖ ≤ |h.im| * S_vert z h f := by
      rwa [him] at hV
                           
    have h_bound := mul_le_mul_of_nonneg_left this (abs_nonneg (h.im))
    exact le_trans hV_rewritten h_bound

  have :=
    calc
      ‖(∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z))
        + Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖
          ≤ ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
            + ‖Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖ := hsplit
      _ = ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
            + ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖ := by simp
      _ ≤ |h.re| * S_max z h f + |h.im| * S_max z h f := add_le_add hH' hV'

  simpa [Err] using this

lemma S_horiz_nonneg (z h : ℂ) (f : ℂ → ℂ) : 0 ≤ S_horiz z h f := by
                                                         
  unfold S_horiz
  apply Real.sSup_nonneg
  intro r hr; rcases hr with ⟨t, ht, rfl⟩; exact norm_nonneg _

lemma S_max_nonneg (z h : ℂ) (f : ℂ → ℂ) : 0 ≤ S_max z h f := by
  unfold S_max
  have h1 : 0 ≤ S_horiz z h f := S_horiz_nonneg z h f
  exact le_trans h1 (le_max_left _ _)

lemma bound_on_Err_ratio
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1)
    (hh : h ≠ 0) :
    ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖ ≤ 2 * S_max z h f := by

  have h_abs_eq : ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖ = ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖ := rfl

  have h1 := bound_on_Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw
                                                                                  
  rw [← add_mul] at h1

  have h_norm_pos : 0 < ‖h‖ := norm_pos_iff.mpr hh

  have h2 : ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h‖ / ‖h‖ ≤
            (|h.re| + |h.im|) * S_max z h f / ‖h‖ := by
    exact div_le_div_of_nonneg_right h1 (le_of_lt h_norm_pos)

  rw [← norm_div] at h2

  have h2' : ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖ ≤
             (|h.re| + |h.im|) / ‖h‖ * S_max z h f := by
    rw [← div_mul_eq_mul_div] at h2
    exact h2

  have h3 : |h.re| + |h.im| ≤ 2 * ‖h‖ := by
                                                                
    calc |h.re| + |h.im|
      ≤ ‖h‖ + ‖h‖ := add_le_add (Complex.abs_re_le_norm h) (Complex.abs_im_le_norm h)
      _ = 2 * ‖h‖ := by ring

  have h4 : (|h.re| + |h.im|) / ‖h‖ ≤ 2 := by
                                                                                         
    rw [div_le_iff₀ h_norm_pos]
    exact h3

  calc ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖
    ≤ (|h.re| + |h.im|) / ‖h‖ * S_max z h f := h2'
    _ ≤ 2 * S_max z h f := mul_le_mul_of_nonneg_right h4 (S_max_nonneg z h f)
open _root_.Filter Topology

lemma abs_horizontal_diff_eq_abs_real (z : ℂ) (t : ℝ) : ‖(t : ℂ) + Complex.I * z.im - z‖ = |t - z.re| := by
                                                           
  have h : (t : ℂ) + Complex.I * z.im - z = (t - z.re : ℂ) := by
    apply Complex.ext_iff.mpr
    constructor
    ·                                      
      simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
                 Complex.I_re, Complex.I_im, Complex.ofReal_im]
      ring
    ·                                       
      simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
                 Complex.I_re, Complex.I_im, Complex.ofReal_re]
      ring

  rw [h]
                                                                         
  rw [← Complex.ofReal_sub]
                                                                             
  rw [Complex.norm_real, Real.norm_eq_abs]

lemma abs_sub_le_of_mem_uIcc (a b t : ℝ) (ht : t ∈ Set.uIcc a b) : |t - a| ≤ |b - a| ∧ |b - t| ≤ |b - a| := by
                                                  
  have h1 : a ≤ b ∨ b ≤ a := le_total a b
  rcases h1 with hle | hle
  ·                             
    have ht' : t ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hle] using ht
    have h_bounds : a ≤ t ∧ t ≤ b := by simpa using ht'
    constructor
    · have h_ta : |t - a| = t - a := by simp [abs_of_nonneg (sub_nonneg.mpr h_bounds.left)]
      have h_ba : |b - a| = b - a := by simp [abs_of_nonneg (sub_nonneg.mpr hle)]
      rw [h_ta, h_ba]
      exact sub_le_sub_right h_bounds.right a
    · have h_bt : |b - t| = b - t := by simp [abs_of_nonneg (sub_nonneg.mpr h_bounds.right)]
      have h_ba : |b - a| = b - a := by simp [abs_of_nonneg (sub_nonneg.mpr hle)]
      rw [h_bt, h_ba]
      exact sub_le_sub_left h_bounds.left b
  ·                         
    have ht' : t ∈ Set.Icc b a := by
      rw [Set.uIcc_comm] at ht
      simpa [Set.uIcc_of_le hle] using ht
    have h_bounds : b ≤ t ∧ t ≤ a := by simpa using ht'
    constructor
    · have h_ta : |t - a| = a - t := by simp [abs_of_nonpos (sub_nonpos.mpr h_bounds.right)]
      have h_ba : |b - a| = a - b := by simp [abs_of_nonpos (sub_nonpos.mpr hle)]
      rw [h_ta, h_ba]
      exact sub_le_sub_left h_bounds.left a
    · have h_bt : |b - t| = t - b := by
        rw [abs_of_nonpos (sub_nonpos.mpr h_bounds.left)]
        ring
      have h_ba : |b - a| = a - b := by simp [abs_of_nonpos (sub_nonpos.mpr hle)]
      rw [h_bt, h_ba]
      exact sub_le_sub_right h_bounds.right b

lemma abs_vertical_core (z h : ℂ) (τ : ℝ) : ‖(h.re : ℝ) + Complex.I * (τ - z.im)‖ ≤ |h.re| + |τ - z.im| := by
                                                                           
  have h1 : ‖(h.re : ℝ) + Complex.I * (τ - z.im)‖ ≤ |((h.re : ℝ) + Complex.I * (τ - z.im)).re| + |((h.re : ℝ) + Complex.I * (τ - z.im)).im| := by
    apply Complex.norm_le_abs_re_add_abs_im

  have h2 : ((h.re : ℝ) + Complex.I * (τ - z.im)).re = h.re := by simp
  have h3 : ((h.re : ℝ) + Complex.I * (τ - z.im)).im = τ - z.im := by simp

  rw [h2, h3] at h1
  exact h1

lemma mem_closedBall_mono_radius {z : ℂ} {r R : ℝ} (hz : z ∈ Metric.closedBall (0 : ℂ) r) (h : r ≤ R) : z ∈ Metric.closedBall (0 : ℂ) R := by
  simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using le_trans (by simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hz) h

lemma tendsto_of_nonneg_local_bound {g : ℂ → ℝ}
  (h_nonneg : ∀ h, 0 ≤ g h)
  (h_loc : ∀ ε > 0, ∃ δ > 0, ∀ h, ‖h‖ < δ → g h ≤ ε) :
  Tendsto g (𝓝 (0:ℂ)) (𝓝 (0:ℝ)) := by
  rw [Metric.tendsto_nhds_nhds]
  intro ε hε
                                                       
  have hε_half : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨δ, hδ_pos, hδ⟩ := h_loc (ε / 2) hε_half
  use δ
  exact ⟨hδ_pos, fun h hh_dist => by
    rw [Real.dist_eq, sub_zero]
    rw [abs_of_nonneg (h_nonneg h)]
    have : g h ≤ ε / 2 := hδ h (by rwa [Complex.dist_eq, sub_zero] at hh_dist)
    linarith⟩

lemma sum_abs_le_two_mul {x y A : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ A) : |x| + |y| ≤ (2:ℝ) * A := by
  have := add_le_add hx hy
  simpa [two_mul] using this

lemma two_norm_lt_of_norm_lt_half {h : ℂ} {δ : ℝ} (_hpos : 0 < δ) (hbound : ‖h‖ < δ/2) : (2:ℝ) * ‖h‖ < δ := by
  have := mul_lt_mul_of_pos_left hbound (by norm_num : (0:ℝ) < 2)
  simpa [two_mul, add_halves] using this

lemma limit_of_S_is_zero
    {r1 R R0 : ℝ}
  (_hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1) :
    Tendsto (fun h => S_max z h f) (𝓝 0) (𝓝 0) := by
                                                                  
  have f_cont_at_z : ContinuousAt f z := by
                                                                     
    have hz_in_R : z ∈ Metric.closedBall (0 : ℂ) R :=
      mem_closedBall_mono_radius hz (le_of_lt hr1_lt_R)
                                        
    exact (hf z hz_in_R).continuousAt

  apply tendsto_of_nonneg_local_bound
  ·                                  
    exact fun h => S_max_nonneg z h f
  ·                                                                   
    intro ε hε_pos
                                        
    rw [Metric.continuousAt_iff] at f_cont_at_z
    obtain ⟨δ₁, hδ₁_pos, hf_bound⟩ := f_cont_at_z ε hε_pos

    use δ₁ / 2
    constructor
    · exact half_pos hδ₁_pos
    · intro h hh_norm

      unfold S_max
      apply max_le

      · unfold S_horiz
                                                 
        apply Real.sSup_le
        ·                                        
          intro r hr
          obtain ⟨t, ht, rfl⟩ := hr

          have key_dist : dist ((t : ℂ) + Complex.I * z.im) z < δ₁ := by
                                                                     
            rw [dist_eq]
                                                                         
            have eq_transform : ‖(t : ℂ) + Complex.I * z.im - z‖ = |t - z.re| := abs_horizontal_diff_eq_abs_real z t
            simp [eq_transform]
                                                                
            have t_bound : |t - z.re| ≤ |(z + h).re - z.re| := (abs_sub_le_of_mem_uIcc z.re (z + h).re t ht).1
            have re_diff_le : |(z + h).re - z.re| ≤ ‖h‖ := by
                                       
              simpa [Complex.add_re, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (Complex.abs_re_le_norm h)
            have h_bound : ‖h‖ < δ₁ / 2 := hh_norm
            calc |t - z.re|
              _ ≤ |(z + h).re - z.re| := t_bound
              _ ≤ ‖h‖ := re_diff_le
              _ < δ₁ / 2 := h_bound
              _ < δ₁ := by linarith
                                              
          have f_dist := hf_bound key_dist
                                                         
          rw [dist_eq] at f_dist
                                 
          exact le_of_lt f_dist
        ·              
          exact le_of_lt hε_pos

      · unfold S_vert
        apply Real.sSup_le
        ·                                        
          intro r hr
          obtain ⟨τ, hτ, rfl⟩ := hr
                                                    
          have key_dist : dist (((z + h).re : ℂ) + Complex.I * τ) z < δ₁ := by
            rw [dist_eq]

            have h_eq : (((z + h).re : ℂ) + Complex.I * τ - z) = (h.re : ℝ) + Complex.I * (τ - z.im) := by
              apply Complex.ext_iff.mpr
              constructor
              · simp [Complex.add_re, Complex.sub_re]
              · simp [Complex.add_im, Complex.sub_im]
            rw [h_eq]
                                                             
            have τ_bound0 : |τ - z.im| ≤ |(z + h).im - z.im| := (abs_sub_le_of_mem_uIcc z.im (z + h).im τ hτ).1
            have im_diff_eq : |(z + h).im - z.im| = |h.im| := by
              simp [Complex.add_im, sub_eq_add_neg, add_assoc]
            have τ_bound : |τ - z.im| ≤ |h.im| := by simpa [im_diff_eq] using τ_bound0
                                                                 
            have vertical_bound : ‖(h.re : ℝ) + Complex.I * (τ - z.im)‖ ≤ |h.re| + |τ - z.im| :=
              abs_vertical_core z h τ
            have sum_bound : |h.re| + |τ - z.im| ≤ |h.re| + |h.im| := by
              exact add_le_add_right τ_bound _
            have norm_bound := sum_abs_le_two_mul (Complex.abs_re_le_norm h) (Complex.abs_im_le_norm h)
            have h_bound : ‖h‖ < δ₁ / 2 := hh_norm
            have final_bound := two_norm_lt_of_norm_lt_half hδ₁_pos h_bound
            calc ‖(h.re : ℝ) + Complex.I * (τ - z.im)‖
              _ ≤ |h.re| + |τ - z.im| := vertical_bound
              _ ≤ |h.re| + |h.im| := sum_bound
              _ ≤ (2 : ℝ) * ‖h‖ := norm_bound
              _ < δ₁ := final_bound
                                              
          have f_dist := hf_bound key_dist
          rw [dist_eq] at f_dist
                                 
          exact le_of_lt f_dist
        ·              
          exact le_of_lt hε_pos

lemma eventually_corner_and_sum_in_closedBall {z : ℂ} {R' : ℝ}
  (hz : ‖z‖ < R') :
  ∀ᶠ h in 𝓝 (0:ℂ),
    (z + h) ∈ Metric.closedBall (0 : ℂ) R' ∧
    (((z + h).re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) R' := by
                         
  have hρ_pos : 0 < R' - ‖z‖ := sub_pos.mpr hz
  have h_small : ∀ᶠ h in 𝓝 (0:ℂ), h ∈ Metric.ball (0 : ℂ) (R' - ‖z‖) :=
    Metric.ball_mem_nhds (0 : ℂ) hρ_pos
  refine h_small.mono ?_
  intro h hhball
  have hnorm_lt : ‖h‖ < R' - ‖z‖ := by
    simpa [Metric.mem_ball, Complex.dist_eq, sub_zero] using hhball
                                              
  have hsum_lt : ‖z‖ + ‖h‖ < R' := by
    have htemp : ‖z‖ + ‖h‖ < ‖z‖ + (R' - ‖z‖) := add_lt_add_right hnorm_lt _
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htemp
  have hzph_le : ‖z + h‖ ≤ R' :=
    le_of_lt (lt_of_le_of_lt (norm_add_le _ _) hsum_lt)
  have hzph_mem : (z + h) ∈ Metric.closedBall (0 : ℂ) R' := by
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hzph_le
                                                                       
  let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
                                                           
  have tri : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
    have := norm_add_le (w - z) z
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
                                                            
  let t : ℝ := (z + h).re
  have hwz_eq : w - z = (t : ℂ) + Complex.I * z.im - z := by
    simp [w, t, sub_eq_add_neg, add_assoc]
  have eq_transform : ‖(t : ℂ) + Complex.I * z.im - z‖ = |t - z.re| :=
    abs_horizontal_diff_eq_abs_real z t
  have t_sub_re : t - z.re = h.re := by
    simp [t, Complex.add_re, sub_eq_add_neg, add_assoc]
  have hwz_abs2 : ‖w - z‖ = |h.re| := by
    simpa [hwz_eq, t_sub_re] using eq_transform
  have hwz_le : ‖w - z‖ ≤ ‖h‖ := by
    simpa [hwz_abs2] using (Complex.abs_re_le_norm h)
  have hw_le'' : ‖w‖ ≤ ‖h‖ + ‖z‖ := by
    exact le_trans tri (add_le_add_left hwz_le _)
  have hw_lt : ‖w‖ < R' := by
    have : ‖h‖ + ‖z‖ < R' := by simpa [add_comm] using hsum_lt
    exact lt_of_le_of_lt hw_le'' this
  have hw_mem : w ∈ Metric.closedBall (0 : ℂ) R' := by
    simpa [w, Metric.mem_closedBall, Complex.dist_eq, sub_zero] using (le_of_lt hw_lt)
  exact And.intro hzph_mem hw_mem

lemma limit_of_Err_ratio_is_zero
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1) :
    Tendsto (fun h => Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h) (𝓝 0) (𝓝 0) := by
                                                 
  set g : ℂ → ℂ := fun h => Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h
                               
  have hS : Tendsto (fun h => S_max z h f) (𝓝 0) (𝓝 0) :=
    limit_of_S_is_zero (r1:=r1) (R:=R) (R0:=R0) hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz
                                        
  have h_upper : Tendsto (fun h => |(2 : ℝ) * S_max z h f|) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous fun x : ℝ => |(2 : ℝ) * x| :=
      (continuous_const.mul continuous_id).abs
    have h0 := hcont.tendsto (0 : ℝ)
    simpa only [Function.comp_def, mul_zero, abs_zero] using h0.comp hS
                                            
  have h_lower_nonneg : ∀ᶠ h in 𝓝 0, 0 ≤ ‖g h‖ :=
    Filter.Eventually.of_forall (fun _ => by simpa [g] using (norm_nonneg (g _)))
                                                                      
  let δ : ℝ := (R - r1) / 2
  have hδ_pos : 0 < δ := by
    have : 0 < R - r1 := sub_pos.mpr hr1_lt_R
    simpa [δ] using half_pos this
  let R' : ℝ := r1 + δ
  have hR'_pos : 0 < R' := by
    have : 0 < r1 + δ := add_pos_of_pos_of_nonneg hr1_pos (le_of_lt hδ_pos)
    simpa [R'] using this
  have hR'_lt_R : R' < R := by
    have hδlt : δ < R - r1 := by
      simpa [δ] using (half_lt_self (sub_pos.mpr hr1_lt_R))
    have : r1 + δ < r1 + (R - r1) := add_lt_add_right hδlt r1
    simpa [R', sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
                                 
  have hz_le_r1 : ‖z‖ ≤ r1 := by
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hz
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hr1_le_R' : r1 ≤ R' := by
      have : 0 ≤ δ := le_of_lt hδ_pos
      simpa [R'] using (le_add_of_nonneg_right this : r1 ≤ r1 + δ)
    have : ‖z‖ ≤ R' := le_trans hz_le_r1 hr1_le_R'
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using this
                                                                                                      
  have h_event : ∀ᶠ h in 𝓝 0, ‖g h‖ ≤ |(2 : ℝ) * S_max z h f| := by
                                                                                          
    have hcorner := eventually_corner_and_sum_in_closedBall (z:=z) (R':=R') (hz := by
                                                    
      have : ‖z‖ ≤ r1 := hz_le_r1
      exact lt_of_le_of_lt this (by simpa [R'] using (lt_add_of_pos_right r1 hδ_pos)))
    refine hcorner.mono ?_
    intro h hh
    have hzh' : z + h ∈ Metric.closedBall (0 : ℂ) R' := hh.1
    have hw' : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) R' := hh.2
    by_cases hh0 : h = 0
    · have : 0 ≤ |(2 : ℝ) * S_max z h f| := abs_nonneg _
      simp [g, hh0, div_zero, norm_zero]
    ·                                        
      have hb :=
        bound_on_Err_ratio (r1:=R') (R:=R) (R0:=R0)
          hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one hf (z:=z) (h:=h) hz' hzh' hw' hh0
      have hb' : ‖g h‖ ≤ 2 * S_max z h f := by
        simpa [g, norm, Err] using hb
      exact le_trans hb' (le_abs_self ((2 : ℝ) * S_max z h f))
                                      
  have h_norm_tendsto : Tendsto (fun h => ‖g h‖) (𝓝 0) (𝓝 0) := by
    refine Filter.Tendsto.squeeze' tendsto_const_nhds h_upper h_lower_nonneg h_event
                                                         
  have h_dist_tendsto : Tendsto (fun h => dist (g h) 0) (𝓝 0) (𝓝 0) := by
    simpa [dist_eq_norm] using h_norm_tendsto
  simpa [g] using (tendsto_iff_dist_tendsto_zero).2 h_dist_tendsto

open Classical
                                                                                      
noncomputable def If_ext
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R)) : ℂ → ℂ :=
  fun w =>
    if h : w ∈ Metric.closedBall (0 : ℂ) r1 then
      If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, h⟩
    else
      0

lemma If_ext_eq_taxicab_of_mem {r1 R R0 : ℝ} (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {w : ℂ} (hw : w ∈ Metric.closedBall (0 : ℂ) r1) :
    If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf w
      = If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩ := by
  classical
  simp [If_ext, hw]

lemma If_taxicab_param_invariance {r1₁ r1₂ R R0 : ℝ}
    (hr1₁_pos : 0 < r1₁) (hr1₁_lt_R : r1₁ < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    (hr1₂_pos : 0 < r1₂) (hr1₂_lt_R : r1₂ < R)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {w : ℂ}
    (hw₁ : w ∈ Metric.closedBall (0 : ℂ) r1₁)
    (hw₂ : w ∈ Metric.closedBall (0 : ℂ) r1₂) :
    If_taxicab hr1₁_pos hr1₁_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw₁⟩
    = If_taxicab hr1₂_pos hr1₂_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw₂⟩ := by

  simp [If_taxicab]

lemma eventually_decomposition_for_ext
  {R' R R0 : ℝ} (hR'_pos : 0 < R') (hR'_lt_R : R' < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  (z : ℂ) (hz : ‖z‖ < R') :
  ∀ᶠ h in 𝓝 (0:ℂ),
    let g := If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf
    g (z + h) - g z = f z * h + Err hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z h := by
                                                                             
  have h_event := eventually_corner_and_sum_in_closedBall (z:=z) (R':=R') hz
  refine h_event.mono ?_
  intro h hh
             
  let g := If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf
                                                        
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have : ‖z‖ ≤ R' := le_of_lt hz
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using this
                                                                           
  have hgzh : g (z + h)
      = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hh.1⟩ := by
    simpa [g] using
      If_ext_eq_taxicab_of_mem (r1:=R') (R:=R) (R0:=R0) hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf (w:=z + h) hh.1
  have hgz : g z
      = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz'⟩ := by
    simpa [g] using
      If_ext_eq_taxicab_of_mem (r1:=R') (R:=R) (R0:=R0) hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf (w:=z) hz'
                                                              
  have H :=
    If_diff_decomposition_final (r1:=R') (R:=R) (R0:=R0)
      hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one (f:=f) (hf:=hf)
      (z:=z) (h:=h)
      (hz:=hz') (hzh:=hh.1) (hw:=hh.2)
                                               
  calc
    g (z + h) - g z
        = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hh.1⟩
          - If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz'⟩ := by
            simp [hgzh, hgz]
    _ = f z * h + Err hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z h := by
      simpa using H

lemma tendsto_Err_ratio_radius (R' R R0 : ℝ) (hR'_pos : 0 < R') (hR'_lt_R : R' < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  {z : ℂ} (hz : ‖z‖ < R') :
  Tendsto (fun h => Err hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z h / h) (𝓝 0) (𝓝 0) := by
                                               
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have : ‖z‖ ≤ R' := le_of_lt hz
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using this
                                                 
  simpa using
    (limit_of_Err_ratio_is_zero (r1:=R') (R:=R) (R0:=R0)
      hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one hf (z:=z) (hz:=hz'))

lemma hasDerivWithinAt_congr_eqOn {f g : ℂ → ℂ} {s : Set ℂ} {z f' : ℂ}
  (hEq : Set.EqOn f g s) (hz : z ∈ s) :
  HasDerivWithinAt g f' s z → HasDerivWithinAt f f' s z := by
  intro hg
  have hfg : ∀ x ∈ s, f x = g x := fun x hx => hEq hx
  simpa using (HasDerivWithinAt.congr_of_mem (h := hg) (hs := hfg) (hx := hz))

lemma differentiableOn_of_hasDerivWithinAt {f : ℂ → ℂ} {s : Set ℂ} {F : ℂ → ℂ}
  (h : ∀ z ∈ s, HasDerivWithinAt f (F z) s z) : DifferentiableOn ℂ f s := by
  intro z hz
  exact (h z hz).differentiableWithinAt

lemma If_ext_agree_on_smallBall {r1 R' R R0 : ℝ}
  (hr1_pos : 0 < r1) (hR'_pos : 0 < R') (hr1_lt_R : r1 < R) (hR'_lt_R : R' < R) (hr1_lt_R' : r1 < R') (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R)) :
  Set.EqOn (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf)
           (If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf)
           (Metric.closedBall (0 : ℂ) r1) := by
  intro w hw
                                                                                
  have hw' : w ∈ Metric.closedBall (0 : ℂ) R' :=
    mem_closedBall_mono_radius (z:=w) (r:=r1) (R:=R') hw (le_of_lt hr1_lt_R')
                                                                  
  have hleft :
      If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf w
        = If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩ := by
    simpa using
      (If_ext_eq_taxicab_of_mem (r1:=r1) (R:=R) (R0:=R0)
        hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf (w:=w) hw)
  have hright :
      If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf w
        = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw'⟩ := by
    simpa using
      (If_ext_eq_taxicab_of_mem (r1:=R') (R:=R) (R0:=R0)
        hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf (w:=w) hw')
                                           
  have hparam :=
    If_taxicab_param_invariance (r1₁:=r1) (r1₂:=R') (R:=R) (R0:=R0)
      hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hR'_pos hR'_lt_R hf (w:=w) hw hw'
                     
  calc
    If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf w
        = If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩ := hleft
    _ = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw'⟩ := hparam
    _ = If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf w := by
          simpa using hright.symm

lemma hasDerivAt_of_local_decomposition' (g : ℂ → ℂ) (z F : ℂ)
  (Err_func : ℂ → ℂ)
  (hdecomp : ∀ᶠ h in 𝓝 (0:ℂ), g (z + h) - g z = F * h + Err_func h)
  (hErr : Tendsto (fun h => Err_func h / h) (𝓝 (0:ℂ)) (𝓝 (0:ℂ))) :
  HasDerivAt g F z := by
                                                             
  have hdecomp_within : ∀ᶠ h in 𝓝[≠] (0:ℂ), g (z + h) - g z = F * h + Err_func h :=
    (hdecomp.filter_mono (nhdsWithin_le_nhds : 𝓝[≠] (0:ℂ) ≤ 𝓝 (0:ℂ)))
                                                                 
  have h_ne0 : ∀ᶠ h in 𝓝[≠] (0:ℂ), h ≠ 0 := by
    filter_upwards [eventually_mem_nhdsWithin (a := (0 : ℂ)) (s := ({0}ᶜ : Set ℂ))] with h hh
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hh
                                                   
  have h_eq_slope : ∀ᶠ h in 𝓝[≠] (0:ℂ),
      h⁻¹ • (g (z + h) - g z) = F + Err_func h / h := by
    refine (hdecomp_within.and h_ne0).mono ?_
    intro h hh
    rcases hh with ⟨hEq, hne⟩
                                                   
    have H0 : h⁻¹ • (g (z + h) - g z) = h⁻¹ • (F * h + Err_func h) := by
      simpa using congrArg (fun x => h⁻¹ • x) hEq
                                     
    have h1 : h⁻¹ * (F * h) = F := by
      have hne' : h ≠ 0 := hne
      calc
        h⁻¹ * (F * h) = F * (h⁻¹ * h) := by
          ac_rfl
        _ = F * 1 := by simp [hne']
        _ = F := by simp
    have h2 : h⁻¹ * Err_func h = Err_func h / h := by
      simp [div_eq_mul_inv, mul_comm]
    calc
      h⁻¹ • (g (z + h) - g z)
          = h⁻¹ • (F * h + Err_func h) := H0
      _ = h⁻¹ * (F * h + Err_func h) := by simp [smul_eq_mul]
      _ = h⁻¹ * (F * h) + h⁻¹ * (Err_func h) := by simp [mul_add]
      _ = F + Err_func h / h := by simp [h1, h2]
                                        
  have hErr_within : Tendsto (fun h => Err_func h / h) (𝓝[≠] (0:ℂ)) (𝓝 (0:ℂ)) :=
    hErr.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℂ) ≤ 𝓝 (0:ℂ))
  have h_const : Tendsto (fun _ : ℂ => F) (𝓝[≠] (0:ℂ)) (𝓝 F) := tendsto_const_nhds
  have h_sum : Tendsto (fun h => F + Err_func h / h) (𝓝[≠] (0:ℂ)) (𝓝 (F + 0)) :=
    h_const.add hErr_within
  have h_target : Tendsto (fun h => h⁻¹ • (g (z + h) - g z)) (𝓝[≠] (0:ℂ)) (𝓝 F) := by
    have := (Filter.tendsto_congr' h_eq_slope).2 h_sum
    simpa [zero_add] using this
                                                             
  exact (hasDerivAt_iff_tendsto_slope_zero).2 h_target

lemma uniqueDiffWithinAt_convex_complex {s : Set ℂ} (hconv : Convex ℝ s)
    (hs : (interior s).Nonempty) {x : ℂ} (hx : x ∈ closure s) :
    UniqueDiffWithinAt ℂ s x := by
                                                                   
  have hR : UniqueDiffWithinAt ℝ s x :=
    uniqueDiffWithinAt_convex (E := ℂ) (conv := hconv) (hs := hs) (x := x) (hx := hx)
                                                       
  have dR : Dense ((Submodule.span ℝ (tangentConeAt ℝ s x) : Submodule ℝ ℂ) : Set ℂ) := by
    simpa using (hR.dense_tangentConeAt)
                                                                  
  have h_tc_subset : tangentConeAt ℝ s x ⊆ tangentConeAt ℂ s x :=
    tangentConeAt_mono_field
                                                                             
  set TC : Set ℂ := tangentConeAt ℂ s x
  set Sℂ : Submodule ℂ ℂ := Submodule.span ℂ TC
  set Sℝ : Submodule ℝ ℂ := Sℂ.restrictScalars ℝ
  have h_span_le : (Submodule.span ℝ (tangentConeAt ℝ s x) : Submodule ℝ ℂ) ≤ Sℝ := by
                                                   
    refine Submodule.span_le.mpr ?_
    intro v hv
    have hv' : v ∈ TC := h_tc_subset hv
    have : v ∈ Sℂ := Submodule.subset_span hv'
    simpa [Sℝ] using this
                                                                            
  have hsubset_sets :
      ((Submodule.span ℝ (tangentConeAt ℝ s x) : Submodule ℝ ℂ) : Set ℂ)
        ⊆ ((Sℂ : Submodule ℂ ℂ) : Set ℂ) := by
    intro z hz
    have hz' : z ∈ Sℝ := h_span_le hz
    simpa [Sℝ] using hz'
  have dC : Dense ((Sℂ : Submodule ℂ ℂ) : Set ℂ) := dR.mono hsubset_sets
                                 
  exact ⟨dC, hx⟩

lemma interior_closedBall_nonempty_of_pos {R : ℝ} (hR_pos : 0 < R) :
    (interior (Metric.closedBall (0 : ℂ) R)).Nonempty := by
                                                               
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    simpa [Metric.mem_ball, Complex.dist_eq, sub_zero] using hR_pos
                                                                  
  have hsub : Metric.ball (0 : ℂ) R ⊆ interior (Metric.closedBall (0 : ℂ) R) :=
    Metric.ball_subset_interior_closedBall
                                   
  exact ⟨0, hsub h0mem⟩

lemma mem_closure_of_mem_closedBall {R : ℝ} {z : ℂ}
  (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
  z ∈ closure (Metric.closedBall (0 : ℂ) R) := by
  exact subset_closure hz

lemma uniqueDiffWithinAt_closedBall_complex_of_mem {R : ℝ} {z : ℂ}
  (hR_pos : 0 < R) (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
  UniqueDiffWithinAt ℂ (Metric.closedBall (0 : ℂ) R) z :=
by
                              
  have hconv : Convex ℝ (Metric.closedBall (0 : ℂ) R) :=
    convex_closedBall (0 : ℂ) R
                                         
  have hnonempty : (interior (Metric.closedBall (0 : ℂ) R)).Nonempty :=
    interior_closedBall_nonempty_of_pos (R := R) hR_pos
                                                
  have hz_cl : z ∈ closure (Metric.closedBall (0 : ℂ) R) :=
    mem_closure_of_mem_closedBall (R := R) (z := z) hz
                                              
  exact uniqueDiffWithinAt_convex_complex hconv hnonempty hz_cl

lemma If_is_differentiable_on
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R)) :
    DifferentiableOn ℂ (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf) (Metric.closedBall (0 : ℂ) r1)
    ∧
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      derivWithin (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf) (Metric.closedBall (0 : ℂ) r1) z = f z := by
  set s : Set ℂ := Metric.closedBall (0 : ℂ) r1
  have hHasDerivWithinAt : ∀ z ∈ s,
      HasDerivWithinAt (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf) (f z) s z := by
    intro z hz
                                                        
    let δ : ℝ := (R - r1) / 2
    have hδ_pos : 0 < δ := by
      have : 0 < R - r1 := sub_pos.mpr hr1_lt_R
      simpa [δ] using half_pos this
    let R' : ℝ := r1 + δ
    have hR'_pos : 0 < R' := by
      have : 0 < r1 + δ := add_pos_of_pos_of_nonneg hr1_pos (le_of_lt hδ_pos)
      simpa [R'] using this
    have hR'_lt_R : R' < R := by
      have hδlt : δ < R - r1 := by
        have : 0 < R - r1 := sub_pos.mpr hr1_lt_R
        simpa [δ] using (half_lt_self this)
      have : r1 + δ < r1 + (R - r1) := add_lt_add_right hδlt r1
      simpa [R', sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hr1_lt_R' : r1 < R' := by
      have : r1 < r1 + δ := by simpa [add_comm, add_left_comm, add_assoc, R', δ] using (lt_of_le_of_lt (le_of_eq rfl) (add_lt_add_right hδ_pos r1))
      simpa [R'] using this
                                       
    have hz_le_r1 : ‖z‖ ≤ r1 := by
      simpa [s, Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hz
    have hz_lt_R' : ‖z‖ < R' := lt_of_le_of_lt hz_le_r1 (by simpa [R'] using (lt_add_of_pos_right r1 hδ_pos))
                                             
    let g := If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf
                                         
    have hdecomp := eventually_decomposition_for_ext (R':=R') (R:=R) (R0:=R0) hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one hf z hz_lt_R'
                                
    have hErr := tendsto_Err_ratio_radius (R':=R') (R:=R) (R0:=R0) hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one hf hz_lt_R'
                                                                
    have hDerivAt_g : HasDerivAt g (f z) z :=
      hasDerivAt_of_local_decomposition' (g := g) (z := z) (F := f z)
        (Err_func := fun h => Err hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z h)
        (hdecomp := by
                                                                                          
          simpa [g] using hdecomp)
        (hErr := by
                                                                         
          simpa using hErr)
                                               
    have hWithin_g : HasDerivWithinAt g (f z) s z := hDerivAt_g.hasDerivWithinAt
                                                      
    have hEq : Set.EqOn (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf)
                        (If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf)
                        s :=
      If_ext_agree_on_smallBall (r1:=r1) (R':=R') (R:=R) (R0:=R0)
        hr1_pos hR'_pos hr1_lt_R hR'_lt_R hr1_lt_R' hR_lt_R0 hR0_lt_one hf
                                                  
    exact hasDerivWithinAt_congr_eqOn (f := If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf)
      (g := g) (s := s) (z := z) (f' := f z) hEq hz hWithin_g
                                 
  refine And.intro ?hdiff ?hderiv
  ·                                                                            
    apply differentiableOn_of_hasDerivWithinAt
    intro z hz
    exact hHasDerivWithinAt z hz
  ·                                   
    intro z hz
    have hUD : UniqueDiffWithinAt ℂ s z :=
      uniqueDiffWithinAt_closedBall_complex_of_mem (R := r1) hr1_pos (z := z) (hz := by simpa [s] using hz)
    have hD := hHasDerivWithinAt z hz
    simpa using hD.derivWithin hUD

open scoped Topology

theorem AnalyticOnNhd.mono_closedBall {B : ℂ → ℂ} {R : ℝ} (R' : ℝ)
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall 0 R)) (hR' : R' < R) :
    AnalyticOnNhd ℂ B (Metric.closedBall 0 R') := by

  exact hB.mono (Metric.closedBall_subset_closedBall (le_of_lt hR'))

lemma I_is_antiderivative
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0) :
    ∃ J : ℂ → ℂ, AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1) ∧
      J 0 = 0 ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z := by
  classical
                                           
  have hB_on_R' : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R') :=
    AnalyticOnNhd.mono_closedBall R' hB hR'_lt_R
  have hderiv_on_R' : AnalyticOnNhd ℂ (deriv B) (Metric.closedBall (0 : ℂ) R') :=
    AnalyticOnNhd.deriv hB_on_R'
  let L : ℂ → ℂ := fun z => deriv B z / B z
  have hL_on_R' : AnalyticOnNhd ℂ L (Metric.closedBall (0 : ℂ) R') := by
    simpa [L] using AnalyticOnNhd.div hderiv_on_R' hB_on_R' hB_ne_zero
                                      
  let δ : ℝ := (R' - r1) / 2
  have hδ_pos : 0 < δ := by
    have : 0 < R' - r1 := sub_pos.mpr hr1_lt_R'
    simpa [δ] using half_pos this
  let R_mid : ℝ := r1 + δ
  have hR_mid_pos : 0 < R_mid := by
    have : 0 < r1 + δ := add_pos_of_pos_of_nonneg hr1_pos (le_of_lt hδ_pos)
    simpa [R_mid] using this
  have hr1_lt_R_mid : r1 < R_mid := by
    have : 0 < δ := hδ_pos
    simpa [R_mid] using (lt_add_of_pos_right r1 this)
  have hR_mid_lt_R' : R_mid < R' := by
    have hδlt : δ < R' - r1 := by
      simpa [δ] using (half_lt_self (sub_pos.mpr hr1_lt_R'))
    have : r1 + δ < r1 + (R' - r1) := add_lt_add_right hδlt r1
    simpa [R_mid, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
                                                                        
  let J : ℂ → ℂ :=
    If_ext (r1 := R_mid) (R := R') (R0 := R) hR_mid_pos hR_mid_lt_R' hR'_lt_R hR_lt_one L hL_on_R'

  have hIf :=
    (If_is_differentiable_on (r1 := R_mid) (R := R') (R0 := R)
      hR_mid_pos hR_mid_lt_R' hR'_lt_R hR_lt_one (f := L) hL_on_R')
  have hDiffOn_mid : DifferentiableOn ℂ J (Metric.closedBall (0 : ℂ) R_mid) := by
    simpa [J] using hIf.1
                                                         
  have hDiffOn_ball_R_mid : DifferentiableOn ℂ J (Metric.ball (0 : ℂ) R_mid) :=
    hDiffOn_mid.mono Metric.ball_subset_closedBall
                                                                       
  have hJ_analyticOnNhd : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1) := by
    intro z hz
                                                               
    have hz_le : dist z (0 : ℂ) ≤ r1 := by
      simpa [Metric.mem_closedBall] using hz
    have hz_lt : dist z (0 : ℂ) < R_mid := lt_of_le_of_lt hz_le hr1_lt_R_mid
    have hz_ball : z ∈ Metric.ball (0 : ℂ) R_mid := by simpa [Metric.mem_ball] using hz_lt
                                                                                
    exact (DifferentiableOn.analyticAt (s := Metric.ball (0 : ℂ) R_mid)
      (f := J) hDiffOn_ball_R_mid (Metric.isOpen_ball.mem_nhds hz_ball))
                
  have h0_in_mid : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R_mid := by
    simpa [Metric.mem_closedBall, dist_self] using (le_of_lt hR_mid_pos)
  have hJ0 : J 0 = 0 := by
    simp [J, If_ext, If_taxicab, h0_in_mid]
                                                           
  have hderiv_eq : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = L z := by
    intro z hz
                                        
    have hz_le : dist z (0 : ℂ) ≤ r1 := by simpa [Metric.mem_closedBall] using hz
    have hz_lt : dist z (0 : ℂ) < R_mid := lt_of_le_of_lt hz_le hr1_lt_R_mid
    have hz_ball : z ∈ Metric.ball (0 : ℂ) R_mid := by simpa [Metric.mem_ball] using hz_lt
    have hz_cb_mid : z ∈ Metric.closedBall (0 : ℂ) R_mid := Metric.ball_subset_closedBall hz_ball
                                                                                      
    have h_cb_nhds : Metric.closedBall (0 : ℂ) R_mid ∈ 𝓝 z :=
      Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz_ball) Metric.ball_subset_closedBall
                                                                                     
    have hDW_eq_L : derivWithin J (Metric.closedBall (0 : ℂ) R_mid) z = L z := by
      simpa [J] using hIf.2 z hz_cb_mid
                                                                                                    
    have hHasWithin : HasDerivWithinAt J (derivWithin J (Metric.closedBall (0 : ℂ) R_mid) z)
        (Metric.closedBall (0 : ℂ) R_mid) z :=
      (hDiffOn_mid z hz_cb_mid).hasDerivWithinAt
    have hHasWithinL : HasDerivWithinAt J (L z) (Metric.closedBall (0 : ℂ) R_mid) z := by
      simpa [hDW_eq_L]
        using hHasWithin
                                                                           
    have hHasDerivAt : HasDerivAt J (L z) z :=
      HasDerivWithinAt.hasDerivAt hHasWithinL h_cb_nhds
                                           
    simpa using hHasDerivAt.deriv
                       
  refine ⟨J, hJ_analyticOnNhd, hJ0, ?_⟩
  intro z hz
  simpa [L] using hderiv_eq z hz

noncomputable def H_auxiliary
    {r1 R' R : ℝ}
    (_hr1_pos : 0 < r1) (_hr1_lt_R' : r1 < R') (_hR'_lt_R : R' < R) (_hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (_hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (_hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    (J : ℂ → ℂ) : ℂ → ℂ :=
  fun z => Complex.exp (J z) / B z

lemma H_at_zero
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (_hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (_hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J 0 = 1 / B 0 := by
  simp [H_auxiliary, hJ_zero]

lemma log_deriv_id
    {r1 R' R : ℝ}
    (_hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (_hR'_lt_R : R' < R) (_hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (_hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (_hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (_hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z * B z = deriv B z := by
  intro z hz
                                                   
  have hzR : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hzR' : dist z (0 : ℂ) ≤ r1 := hz
    have hR'_le : r1 ≤ R' := le_of_lt (hr1_lt_R')
    have hzR'' : dist z (0 : ℂ) ≤ R' := le_trans hzR' hR'_le
    simpa using hzR''
  have hBnz : B z ≠ 0 := hB_ne_zero z hzR
  have hJd := hJ_deriv z hz
  have hmult := congrArg (fun t => t * B z) hJd
  have hR2 : (deriv B z / B z) * B z = deriv B z * B z / B z := by
    simpa using (div_mul_eq_mul_div (deriv B z) (B z) (B z))
  have hmult' : deriv J z * B z = deriv B z * B z / B z := by
    simpa [hR2] using hmult
  have hdiv' : deriv B z * B z / B z = deriv B z := by
    field_simp [hBnz]
  calc
    deriv J z * B z = deriv B z * B z / B z := hmult'
    _ = deriv B z := by simpa using hdiv'

lemma log_deriv_identity
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z * B z - deriv B z = 0 := by
  intro z hz
  have h_eq := log_deriv_id hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  rw [h_eq]
  simp

lemma H_derivative_quotient_rule
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (_hJ_zero : J 0 = 0)
    (_hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z =
      (deriv (fun w => Complex.exp (J w)) z * B z - deriv B z * Complex.exp (J z)) / (B z)^2 := by
  intro z hz
                                        
  have hzR : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hzR' : dist z (0 : ℂ) ≤ r1 := hz
    have hR_le : r1 ≤ R' := le_of_lt (hr1_lt_R')
    have hzR'' : dist z (0 : ℂ) ≤ R' := le_trans hzR' hR_le
    simpa using hzR''
                                                      
  have hB_nz : B z ≠ 0 := hB_ne_zero z hzR
  have hB' : AnalyticOnNhd ℂ B (Metric.closedBall 0 R') := by
    apply AnalyticOnNhd.mono_closedBall R' hB
    assumption
  have hB_diff : DifferentiableAt ℂ B z := (hB' z hzR).differentiableAt
  have hJ_diff : DifferentiableAt ℂ J z := (hJ z hz).differentiableAt
  have hF_diff : DifferentiableAt ℂ (fun w => Complex.exp (J w)) z := hJ_diff.cexp
                                            
  have h := deriv_div (hc := hF_diff) (hd := hB_diff) (hx := hB_nz)
  unfold H_auxiliary
  simpa only [Pi.div_def, mul_comm] using h

lemma exp_I_derivative_chain_rule
    {r1 R' R : ℝ}
    (_hr1_pos : 0 < r1) (_hr1_lt_R' : r1 < R') (_hR'_lt_R : R' < R) (_hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (_hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (_hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (_hJ_zero : J 0 = 0)
    (_hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (fun w => Complex.exp (J w)) z = deriv J z * Complex.exp (J z) := by
  intro z hz
  have hJ_diff : DifferentiableAt ℂ J z := (hJ z hz).differentiableAt
  have hJ_has : HasDerivAt J (deriv J z) z := hJ_diff.hasDerivAt
  have hcomp := (Complex.hasDerivAt_exp (J z)).comp z hJ_has
                           
  simpa only [Function.comp_def, mul_comm] using hcomp.deriv

lemma H_derivative_calc
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z =
      (deriv J z * B z - deriv B z) * Complex.exp (J z) / (B z)^2 := by
  intro z hz
                                 
  have hquot := H_derivative_quotient_rule hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
                                            
  have hchain := exp_I_derivative_chain_rule hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
                                             
  rw [hquot, hchain]

  have h1 : deriv J z * Complex.exp (J z) * B z - deriv B z * Complex.exp (J z) =
           Complex.exp (J z) * (deriv J z * B z - deriv B z) := by ring
  rw [h1]

  ring

lemma H_derivative_is_zero
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z = 0 := by
  intro z hz
  have hcalc :=
    H_derivative_calc hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  have hident :=
    log_deriv_identity hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  simpa [hident] using hcalc

lemma zero_mem_closedBall_zero_radius {r1 : ℝ} (hr1 : 0 ≤ r1) : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) r1 := by
  simpa [Metric.mem_closedBall, dist_eq_norm] using hr1

lemma H_deriv_zero_on_closedBall
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z = 0 := by
  simpa using
    (H_derivative_is_zero hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv)

lemma H_auxiliary_differentiableOn_closedBall
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1)) :
    DifferentiableOn ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (Metric.closedBall (0 : ℂ) r1) :=
by
                                              
  have hsubset : Metric.closedBall (0 : ℂ) r1 ⊆ Metric.closedBall (0 : ℂ) R := by
    intro z hz
    have hz' : dist z (0 : ℂ) ≤ r1 := by
      simpa [Metric.mem_closedBall] using hz
    have hle : r1 ≤ R := le_of_lt (lt_trans hr1_lt_R' hR'_lt_R)
    have : dist z (0 : ℂ) ≤ R := le_trans hz' hle
    simpa [Metric.mem_closedBall] using this
                                                    
  have hJ_diff : DifferentiableOn ℂ J (Metric.closedBall (0 : ℂ) r1) :=
    hJ.differentiableOn
  have hB_diff_r1 : DifferentiableOn ℂ B (Metric.closedBall (0 : ℂ) r1) :=
    (hB.differentiableOn).mono hsubset
                                                         
  have hExp_diff : DifferentiableOn ℂ Complex.exp (Set.univ : Set ℂ) :=
    (Complex.differentiable_exp.differentiableOn)
  have hExp_comp : DifferentiableOn ℂ (fun z => Complex.exp (J z)) (Metric.closedBall (0 : ℂ) r1) := by
    refine hExp_diff.comp hJ_diff ?_
    intro x hx; simp
                                                 
  have hB_ne_zero_r1 : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, B z ≠ 0 := by
    intro z hz; exact hB_ne_zero z (by
    have x : Metric.closedBall 0 r1 ⊆ Metric.closedBall 0 R' := Metric.closedBall_subset_closedBall (le_of_lt hr1_lt_R')
    simp
    simp at hz
    linarith
    )
                                                
  have hdiv : DifferentiableOn ℂ (fun z => Complex.exp (J z) / B z)
      (Metric.closedBall (0 : ℂ) r1) :=
    hExp_comp.div hB_diff_r1 hB_ne_zero_r1
                                     
  unfold H_auxiliary
  exact hdiv

lemma hasDerivAt_H_auxiliary_zero_on_closedBall
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      HasDerivAt (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) 0 z := by
  intro z hz
                                               
  have hzR : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hzR' : dist z (0 : ℂ) ≤ r1 := by
      simpa [Metric.mem_closedBall] using hz
    have hR_le : r1 ≤ R' := le_of_lt (hr1_lt_R')
    have hzR'' : dist z (0 : ℂ) ≤ R' := le_trans hzR' hR_le
    simpa [Metric.mem_closedBall] using hzR''
  have hBnz : B z ≠ 0 := hB_ne_zero z (hzR)
                                               
  have hJ_anal : AnalyticAt ℂ J z := hJ z hz
  have hExp_diff_at_Jz : DifferentiableAt ℂ Complex.exp (J z) :=
    Complex.differentiableAt_exp
  have hc_diff : DifferentiableAt ℂ (fun w => Complex.exp (J w)) z :=
    hExp_diff_at_Jz.comp z hJ_anal.differentiableAt

  have hB' : AnalyticOnNhd ℂ B (Metric.closedBall 0 R') := by
    apply AnalyticOnNhd.mono_closedBall R' hB
    assumption
  have hd_diff : DifferentiableAt ℂ B z := (hB' z hzR).differentiableAt
                                                                      
  have hH_diff : DifferentiableAt ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z := by
    unfold H_auxiliary
    convert (preTransparency := .instances) hc_diff.div hd_diff hBnz using 1
    all_goals try with_reducible_and_instances rfl
  have hH_has : HasDerivAt (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z) z :=
    hH_diff.hasDerivAt
  have hderiv0 : deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z = 0 :=
    H_deriv_zero_on_closedBall hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  simpa [hderiv0] using hH_has

lemma fderivWithin_eq_zero_of_derivWithin_eq_zero {s : Set ℂ} {f : ℂ → ℂ} {x : ℂ}
    (_hdiff : DifferentiableWithinAt ℂ f s x)
    (hderiv : derivWithin f s x = 0) :
    fderivWithin ℂ f s x = 0 := by
  rw [← toSpanSingleton_derivWithin, hderiv]
  simp

lemma hasDerivWithinAt_of_hasDerivAt {f : ℂ → ℂ} {s : Set ℂ} {x : ℂ}
    (h : HasDerivAt f 0 x) : HasDerivWithinAt f 0 s x := by
  simpa using h.hasDerivWithinAt

lemma H_auxiliary_fderivWithin_zero_on_closedBall
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      fderivWithin ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
        (Metric.closedBall (0 : ℂ) r1) z = 0 :=
by
  intro z hz
                                                                                   
  have hHasAt :=
    hasDerivAt_H_auxiliary_zero_on_closedBall hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero
      hJ hJ_zero hJ_deriv z hz
  have hHasWithin :
      HasDerivWithinAt (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) 0
        (Metric.closedBall (0 : ℂ) r1) z :=
    hasDerivWithinAt_of_hasDerivAt hHasAt
                                         
  have hdiff : DifferentiableWithinAt ℂ
      (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (Metric.closedBall (0 : ℂ) r1) z :=
    hHasWithin.differentiableWithinAt
                                                                            
  classical
  have hderivWithin0 :
      derivWithin (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
        (Metric.closedBall (0 : ℂ) r1) z = 0 := by
    by_cases hUDc : UniqueDiffWithinAt ℂ (Metric.closedBall (0 : ℂ) r1) z
    · simpa using hHasWithin.derivWithin hUDc
    · simpa using
        (derivWithin_zero_of_not_uniqueDiffWithinAt
          (𝕜 := ℂ)
          (f := H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
          (s := Metric.closedBall (0 : ℂ) r1) (x := z) hUDc)
                                              
  exact fderivWithin_eq_zero_of_derivWithin_eq_zero hdiff hderivWithin0

lemma H_is_constant
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J z =
      H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J 0 := by
  intro z hz
                              
  have hs : Convex ℝ (Metric.closedBall (0 : ℂ) r1) := by
    simpa using (convex_closedBall (0 : ℂ) r1)
                                              
  have hdiff : DifferentiableOn ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (Metric.closedBall (0 : ℂ) r1) :=
    H_auxiliary_differentiableOn_closedBall hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ
                                            
  have hfderiv0 : ∀ x ∈ Metric.closedBall (0 : ℂ) r1,
      fderivWithin ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
        (Metric.closedBall (0 : ℂ) r1) x = 0 :=
    H_auxiliary_fderivWithin_zero_on_closedBall hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv
                                 
  have h0mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) r1 :=
    zero_mem_closedBall_zero_radius (le_of_lt hr1_pos)
                                           
  have hbound : ∀ x ∈ Metric.closedBall (0 : ℂ) r1,
      ‖fderivWithin ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
          (Metric.closedBall (0 : ℂ) r1) x‖ ≤ 0 := by
    intro x hx
    simp [hfderiv0 x hx]
  have hineq :=
    Convex.norm_image_sub_le_of_norm_fderivWithin_le (𝕜 := ℂ)
      (f := H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (s := Metric.closedBall (0 : ℂ) r1) (x := (0 : ℂ)) (y := z)
      hdiff hbound hs h0mem hz
  have hzero : H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J z -
      H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J 0 = 0 := by
    have : ‖H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J z -
        H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J 0‖ ≤ 0 := by
      simpa using hineq
    simpa [norm_le_zero_iff] using this
  simpa [sub_eq_add_neg] using sub_eq_zero.mp hzero

lemma H_is_one
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J z = 1 / B 0 := by
  intro z hz
  have hconst := H_is_constant hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  have h0 := H_at_zero hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv
  simpa [h0] using hconst

lemma analytic_log_exists
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1, B z = B 0 * Complex.exp (J z) := by
  intro z hz
                                             
  have hH_const := H_is_one hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
                                         
  unfold H_auxiliary at hH_const
                                          
  have hzR : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hzR' : dist z (0 : ℂ) ≤ r1 := hz
    have hR_le : r1 ≤ R := le_of_lt (lt_trans hr1_lt_R' hR'_lt_R)
    exact le_trans hzR' (by linarith)
  have hBnz : B z ≠ 0 := hB_ne_zero z hzR
  have hR_pos : 0 < R := lt_trans (lt_trans hr1_pos hr1_lt_R') hR'_lt_R
  have hB0nz : B 0 ≠ 0 := hB_ne_zero 0 (by
    simp [Metric.closedBall, dist_zero_right]
    exact le_of_lt (by linarith))
                                                  
  have heq : Complex.exp (J z) * B 0 = B z := by
    field_simp [hBnz, hB0nz] at hH_const
    exact hH_const
                                              
  rw [← heq, mul_comm]

lemma modulus_of_exp_I
    {r1 R' R : ℝ}
    (_hr1_pos : 0 < r1) (_hr1_lt_R' : r1 < R') (_hR'_lt_R : R' < R) (_hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (_hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (_hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (_hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (_hJ_zero : J 0 = 0)
    (_hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      norm (Complex.exp (J z)) = Real.exp (Complex.re (J z)) := by
  intro z hz
  exact Complex.norm_exp (J z)

lemma modulus_of_B_product_form
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      norm (B z) = norm (B 0) * norm (Complex.exp (J z)) := by
  intro z hz
  have hBform := analytic_log_exists hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
                          
  simpa [norm_mul] using (congrArg norm hBform)

lemma modulus_of_exp_log
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      norm (B z) = norm (B 0) * Real.exp (Complex.re (J z)) := by
  intro z hz
  rw [modulus_of_B_product_form hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz]
  rw [modulus_of_exp_I hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz]

lemma log_modulus_as_sum
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      Real.log (norm (B z)) =
      Real.log (norm (B 0)) + Real.log (Real.exp (Complex.re (J z))) := by
  intro z hz
                                                     
  have h_eq := modulus_of_exp_log hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
                                                         
  rw [h_eq, Real.log_mul]
  ·                       
                                                                            
    simp
    apply hB_ne_zero
                                           
    rw [Metric.mem_closedBall, dist_self]
    linarith
  ·                                        
    exact Real.exp_ne_zero _

lemma real_log_of_modulus_difference
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      Real.log (norm (B z)) - Real.log (norm (B 0)) = Complex.re (J z) := by
  intro z hz
                                     
  have h_sum := log_modulus_as_sum hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
                                    
  rw [h_sum]
                                                                       
  rw [Real.log_exp]
  ring

theorem log_of_analytic
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0) :
    ∃ J_B : ℂ → ℂ,
      AnalyticOnNhd ℂ J_B (Metric.closedBall (0 : ℂ) r1) ∧
      J_B 0 = 0 ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J_B z = deriv B z / B z) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) r1,
        Real.log (norm (B z)) - Real.log (norm (B 0)) = Complex.re (J_B z)) := by
  have hB_ne_zero_R' : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0 := hB_ne_zero
  obtain ⟨J_B, hJ, hJ0, hJderiv⟩ :=
    I_is_antiderivative hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero_R'
  refine ⟨J_B, hJ, hJ0, hJderiv, ?_⟩
  intro z hz
  simpa using
    (real_log_of_modulus_difference hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ0 hJderiv z hz)

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.Erdos970_PNT2_LogDerivative
attribute [-simp] _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970


lemma DRinD1 (R : ℝ) (_hR : 0 < R) (hR' : R < 1) :
    Metric.closedBall (0 : ℂ) R ⊆ Metric.ball (0 : ℂ) 1 := by
  exact Metric.closedBall_subset_ball hR'
def zerosetKfR (R : ℝ) (_hR : 0 < R) (f : ℂ → ℂ) : Set ℂ :=
  {ρ : ℂ | ρ ∈ Metric.closedBall (0 : ℂ) R ∧ f ρ = 0}
lemma lemKinDR (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) :
    zerosetKfR R hR f ⊆ Metric.closedBall (0 : ℂ) R := by
  intro ρ hρ

  rw [zerosetKfR] at hρ
                                                                     
  exact hρ.1
lemma lemKRinK1 (R : ℝ) (hR : 0 < R) (hR' : R < 1) (f : ℂ → ℂ) :
    zerosetKfR R hR f ⊆ {ρ : ℂ | ρ ∈ Metric.ball (0 : ℂ) 1 ∧ f ρ = 0} := by
  intro ρ hρ
  simp only [zerosetKfR, Set.mem_ofPred_eq] at hρ ⊢
  constructor
  · exact DRinD1 R hR hR' hρ.1
  · exact hρ.2

lemma lem_bolzano_weierstrass {D : Set ℂ} (hD : IsCompact D) {Z : Set ℂ} (hZ_inf : Z.Infinite) (hZ_sub_D : Z ⊆ D) :
    ∃ ρ₀ ∈ D, AccPt ρ₀ (Filter.principal Z) :=
  Set.Infinite.exists_accPt_of_subset_isCompact hZ_inf hD hZ_sub_D
lemma lem_zeros_have_limit_point (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) (h_Kf_inf : Set.Infinite (zerosetKfR R hR f)) :
    ∃ ρ₀ ∈ Metric.closedBall (0 : ℂ) R, AccPt ρ₀ (Filter.principal (zerosetKfR R hR f)) := by
  apply lem_bolzano_weierstrass
  ·                                                
    rw [← lem_ballDR R hR]
    exact lem_DRcompact R hR
  · exact h_Kf_inf
  · exact lemKinDR R hR f

open _root_.Filter Metric _root_.Set Bornology _root_.Function

lemma lem_identity_theorem (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (ρ₀ : ℂ) (hρ₀_in_D1 : ρ₀ ∈ Metric.ball (0 : ℂ) 1)
    (h_acc : AccPt ρ₀ (Filter.principal ({ρ : ℂ | ρ ∈ Metric.ball (0 : ℂ) 1 ∧ f ρ = 0}))) :
    EqOn f 0 (Metric.ball (0 : ℂ) 1) := by
                                                 
  have h_subset : Metric.ball (0 : ℂ) 1 ⊆ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall
                                                        
  have hf_open : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1) := AnalyticOnNhd.mono hf h_subset
                                                         
  have h_conn : IsConnected (Metric.ball (0 : ℂ) 1) := Metric.isConnected_ball (by norm_num : (0 : ℝ) < 1)
  have h_preconn : IsPreconnected (Metric.ball (0 : ℂ) 1) := h_conn.isPreconnected
                                                     
  have h_zeros_subset : {ρ : ℂ | ρ ∈ Metric.ball (0 : ℂ) 1 ∧ f ρ = 0} ⊆ {z | f z = 0} := by
    intro z hz
    exact hz.2
                                                                                           
  have h_acc_zero : AccPt ρ₀ (Filter.principal ({z | f z = 0})) := by
    exact AccPt.mono h_acc (principal_mono.2 h_zeros_subset)
                                                                                                  
  have h_closure : ρ₀ ∈ closure ({z | f z = 0} \ {ρ₀}) := by
                                                                                
    have h_cluster : ClusterPt ρ₀ (Filter.principal ({z | f z = 0} \ {ρ₀})) :=
      (accPt_principal_iff_clusterPt).mp h_acc_zero
    exact (mem_closure_iff_clusterPt).2 h_cluster
                               
  exact AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure hf_open h_preconn hρ₀_in_D1 h_closure
lemma lem_identity_theoremR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (ρ₀ : ℂ) (hρ₀_in_DR : ρ₀ ∈ Metric.closedBall (0 : ℂ) R)
    (h_acc : AccPt ρ₀ (Filter.principal ({ρ : ℂ | ρ ∈ Metric.ball (0 : ℂ) 1 ∧ f ρ = 0}))) :
    EqOn f 0 (Metric.ball (0 : ℂ) 1) := by
  have hρ₀_in_D1 : ρ₀ ∈ Metric.ball (0 : ℂ) 1 := DRinD1 R hR hR' hρ₀_in_DR
  exact lem_identity_theorem f hf ρ₀ hρ₀_in_D1 h_acc
lemma lem_identity_theoremKR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (h_exists_rho0 : ∃ ρ₀ ∈ Metric.closedBall (0 : ℂ) R, AccPt ρ₀ (Filter.principal (zerosetKfR R hR f))) :
    EqOn f 0 (Metric.ball (0 : ℂ) 1) := by
                                
  obtain ⟨ρ₀, hρ₀_in_R, h_acc⟩ := h_exists_rho0
                                
  apply lem_identity_theoremR R hR hR' f hf ρ₀ hρ₀_in_R
                                                                    
  exact AccPt.mono h_acc (principal_mono.2 (lemKRinK1 R hR hR' f))
lemma lem_identity_infiniteKR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (h_Kf_inf : Set.Infinite (zerosetKfR R hR f)) :
    EqOn f 0 (Metric.ball (0 : ℂ) 1) := by
  have h_exists_rho0 := lem_zeros_have_limit_point R hR f h_Kf_inf
  exact lem_identity_theoremKR R hR hR' f hf h_exists_rho0
lemma lem_Contra_finiteKR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (h_exists_nonzero : ∃ z ∈ Metric.ball (0 : ℂ) 1, f z ≠ 0) :
    Set.Finite (zerosetKfR R hR f) := by
                                                  
  by_contra h_not_finite

  have h_Kf_inf : Set.Infinite (zerosetKfR R hR f) := h_not_finite
                                  
  have h_eq_zero := lem_identity_infiniteKR R hR hR' f hf h_Kf_inf

  obtain ⟨z, hz_in_ball, hz_nonzero⟩ := h_exists_nonzero
  have h_f_z_zero : f z = 0 := h_eq_zero hz_in_ball
  exact hz_nonzero h_f_z_zero

open Classical

lemma lem_frho_zero (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (_hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    f ρ = 0 := h_rho_in_KfR1.2

lemma lem_m_rho_is_nat (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hR_lt_1 : R < 1) :
    ∀ (ρ : ℂ) (_h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f),
    analyticOrderAt f ρ ≠ ⊤ := by
  intro ρ h_rho_in_KfR1
                                           
  have hρ_closed_R1 : ρ ∈ Metric.closedBall (0 : ℂ) R1 := h_rho_in_KfR1.1
                                    
  have hR1_le_R : R1 ≤ R := by linarith
  have hR1_lt_one : R1 < 1 := by linarith
                       
  have hρ_ball1 : ρ ∈ Metric.ball (0 : ℂ) 1 := by
    have hdist_le : dist ρ (0 : ℂ) ≤ R1 := (Metric.mem_closedBall.mp hρ_closed_R1)
    have hdist_lt : dist ρ (0 : ℂ) < 1 := by linarith
    simpa [Metric.mem_ball] using hdist_lt
                       
  have hf_at_ρ : AnalyticAt ℂ f ρ := by
                                      
    have hsubset : Metric.closedBall (0 : ℂ) R1 ⊆ Metric.closedBall (0 : ℂ) 1 :=
      Metric.closedBall_subset_closedBall (le_of_lt hR1_lt_one)
    have hρ_closed1 : ρ ∈ Metric.closedBall (0 : ℂ) 1 := hsubset hρ_closed_R1
    exact h_f_analytic ρ hρ_closed1
                                                    
  by_contra htop
                                                           
  have h_eventually_zero : ∀ᶠ z in nhds ρ, f z = 0 := by
    have h_equiv : (analyticOrderAt f ρ = ⊤ ↔ ∀ᶠ z in nhds ρ, f z = 0) := by
      simp [analyticOrderAt, hf_at_ρ]
    exact h_equiv.mp (by simpa using htop)
                                                     
  have hf_on_ball : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have hz' : z ∈ Metric.closedBall (0 : ℂ) 1 :=
      (Metric.ball_subset_closedBall : Metric.ball (0 : ℂ) 1 ⊆ Metric.closedBall (0 : ℂ) 1) hz
    exact h_f_analytic z hz'
                                  
  have h_preconn : IsPreconnected (Metric.ball (0 : ℂ) 1) :=
    (Metric.isConnected_ball (by exact (zero_lt_one : (0 : ℝ) < 1))).isPreconnected
                                                  
  have h_eqOn_zero : Set.EqOn f 0 (Metric.ball (0 : ℂ) 1) :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hf_on_ball h_preconn hρ_ball1
      h_eventually_zero
                                 
  have h0_in_ball : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    simp [Metric.mem_ball]
  have : f 0 = 0 := by
    have h := h_eqOn_zero h0_in_ball
    simpa [Pi.zero_apply] using h
  exact h_f_nonzero_at_zero this

lemma analyticOrderAt_ge_one_of_zero (f : ℂ → ℂ) (z : ℂ) (hf : AnalyticAt ℂ f z) (hz : f z = 0) (hfinite : analyticOrderAt f z ≠ ⊤) : analyticOrderAt f z ≥ 1 := by
                                                                 
  have h_order_ne_zero : analyticOrderAt f z ≠ 0 := by
    intro h_order_zero
                                                              
    have h_f_ne_zero : f z ≠ 0 := by
      rw [← AnalyticAt.analyticOrderAt_eq_zero hf]
      exact h_order_zero
                                    
    exact h_f_ne_zero hz
                                                                      
  cases' h : analyticOrderAt f z with n
  ·                                 
                               
    rw [h] at hfinite
    exact False.elim (hfinite rfl)
  ·                                                 

    rw [h] at h_order_ne_zero
    have n_ne_zero : n ≠ 0 := by
      intro n_zero
      rw [n_zero, Nat.cast_zero] at h_order_ne_zero
      exact h_order_ne_zero rfl
                                 
    have n_ge_one : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr n_ne_zero
                            
    exact Nat.cast_le.mpr n_ge_one

lemma lem_m_rho_ge_1 (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hR_lt_1 : R < 1) :
    ∀ (ρ : ℂ) (_h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f),
    analyticOrderAt f ρ ≥ 1 := by
  intro ρ h_rho_in_KfR1
                                                     
  have h_f_rho_zero : f ρ = 0 := lem_frho_zero R R1 hR1_pos hR1_lt_R f h_f_analytic ρ h_rho_in_KfR1
                                                        
  have h_order_finite : analyticOrderAt f ρ ≠ ⊤ := lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 ρ h_rho_in_KfR1
                       
  have h_f_analytic_at_rho : AnalyticAt ℂ f ρ := by
    apply h_f_analytic
                                            
    have h_R1_lt_1 : R1 < 1 := by linarith
    have h_rho_in_R1 : ρ ∈ Metric.closedBall 0 R1 := h_rho_in_KfR1.1
    exact Metric.closedBall_subset_closedBall (le_of_lt h_R1_lt_1) h_rho_in_R1
                                                                          
  exact analyticOrderAt_ge_one_of_zero f ρ h_f_analytic_at_rho h_f_rho_zero h_order_finite

noncomputable def Cf
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (_hR1_lt_R : R1 < R)
    (_hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))                                                        
    (z : ℂ) : ℂ :=
  if hz : z ∈ zerosetKfR R1 (by linarith) f then
    h_σ z z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase z), (z - ρ) ^ (analyticOrderAt f ρ).toNat
  else
    f z / ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat

lemma lem_denomAnalAt (S : Finset ℂ) (n : ℂ → ℕ)
    (_hn_pos : ∀ s ∈ S, 0 < n s) (w : ℂ) (hw : w ∉ S) :
    AnalyticAt ℂ (fun z => ∏ s ∈ S, (z - s) ^ (n s)) w ∧
    (∏ s ∈ S, (w - s) ^ (n s)) ≠ 0 := by
  constructor
  ·                          
                                 
    let f : ℂ → ℂ → ℂ := fun s z => (z - s) ^ (n s)
    have h_each_analytic : ∀ s ∈ S, AnalyticAt ℂ (f s) w := by
      intro s hs
      simp only [f]
                                                               
      have h_sub : AnalyticAt ℂ (fun z => z - s) w := by
        exact AnalyticAt.sub analyticAt_id analyticAt_const
                                              
      exact h_sub.pow (n s)
    have h_prod := Finset.analyticAt_prod S h_each_analytic
    convert (preTransparency := .instances) h_prod using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (ext z; simp [f])
  ·                                
    apply Finset.prod_ne_zero_iff.mpr
    intro s hs
    apply pow_ne_zero
                     
    intro h_eq
                                         
    have h_w_eq_s : w = s := by
      rwa [← sub_eq_zero]
                                              
    rw [h_w_eq_s] at hw
    exact hw hs

lemma lem_ratioAnalAt (w : ℂ) (R R1 : ℝ) (_hR1_lt_R : R1 < R) (_hR_lt_1 : R < 1)
    (h : ℂ → ℂ) (hh : AnalyticAt ℂ h w)
    (S : Finset ℂ) (_hS : ↑S ⊆ Metric.closedBall (0 : ℂ) R1) (n : ℂ → ℕ)
    (hn_pos : ∀ s ∈ S, 0 < n s)
    (hw : w ∈ Metric.closedBall (0 : ℂ) 1 \ ↑S) :
    AnalyticAt ℂ (fun z => h z / ∏ s ∈ S, (z - s) ^ (n s)) w := by
  classical
                                                  
  have hden := lem_denomAnalAt (S := S) (n := n)
      (_hn_pos := hn_pos) (w := w)
      (hw := by simpa using hw.2)
                                                   
  exact AnalyticAt.div hh hden.1 hden.2

lemma lem_Cf_analytic_off_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (_h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 (by linarith) f) :
    AnalyticAt ℂ (Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) z := by

  have h_ratio_analytic : AnalyticAt ℂ (fun w => f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ (analyticOrderAt f ρ).toNat) z := by
    apply lem_ratioAnalAt z R R1 hR1_lt_R hR_lt_1 f

    · apply h_f_analytic
      exact Metric.closedBall_subset_closedBall (le_of_lt hR_lt_1) hz.1

    · intro ρ hρ
      have h_mem : ρ ∈ zerosetKfR R1 (by linarith) f := h_finite_zeros.mem_toFinset.mp hρ
      exact h_mem.1

    · intro s hs
      have h_s_in_zeros : s ∈ zerosetKfR R1 (by linarith) f := h_finite_zeros.mem_toFinset.mp hs
      have h_order_ge_1 := lem_m_rho_ge_1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 s h_s_in_zeros
      have h_order_finite := lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 s h_s_in_zeros

      cases' h_cases : analyticOrderAt f s with n
      ·                    
        rw [h_cases] at h_order_finite
        exact False.elim (h_order_finite rfl)
      ·                               
        have n_ge_1 : n ≥ 1 := by
          rw [h_cases] at h_order_ge_1
          exact Nat.cast_le.mp h_order_ge_1
        simp
        exact Nat.pos_iff_ne_zero.mpr (ne_of_gt n_ge_1)

    · constructor
      · exact Metric.closedBall_subset_closedBall (le_of_lt hR_lt_1) hz.1
      ·                                     
        intro h_z_in_finset
        have h_z_in_zeros : z ∈ zerosetKfR R1 (by linarith) f := h_finite_zeros.mem_toFinset.mp h_z_in_finset
        exact hz.2 h_z_in_zeros

  have h_eventually_eq : (fun w => f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ (analyticOrderAt f ρ).toNat) =ᶠ[nhds z]
    (fun w => Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ w) := by
                                                           
    have hz_not_in : z ∉ zerosetKfR R1 (by linarith) f := hz.2
    have h_open : IsOpen (Set.compl (zerosetKfR R1 (by linarith) f)) := h_finite_zeros.isClosed.isOpen_compl
    apply Filter.eventually_of_mem (h_open.mem_nhds hz_not_in)
    intro w hw_not_in_compl
                                                              
    have hw_not_in_zeros : w ∉ zerosetKfR R1 (by linarith) f := hw_not_in_compl
                                                         
    show f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ (analyticOrderAt f ρ).toNat =
         Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ w
                                                                          
    rw [Cf, dif_neg hw_not_in_zeros]

  exact h_ratio_analytic.congr h_eventually_eq

lemma lem_Cf_at_sigma_onK
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (_h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∀ᶠ z in nhds σ, z = σ →
      Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      h_σ z z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
  refine Filter.Eventually.of_forall ?_
  intro z hz
  subst hz
  simp [Cf, hσ]

lemma lem_Cf_at_sigma_offK0
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∀ᶠ z in nhds σ, z ≠ σ →
      Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z /
      ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
                                        
  obtain ⟨h_σ_analytic, h_σ_ne_zero, h_f_eq⟩ := h_σ_spec σ hσ

  have h_σ_eventually_nonzero : ∀ᶠ z in nhds σ, h_σ σ z ≠ 0 := by
    have h_cont : ContinuousAt (h_σ σ) σ := h_σ_analytic.continuousAt
    exact h_cont.eventually_ne h_σ_ne_zero

  have h_f_eventually_nonzero : ∀ᶠ z in nhds σ, z ≠ σ → f z ≠ 0 := by
    filter_upwards [h_f_eq, h_σ_eventually_nonzero] with z h_fz_eq h_σz_nonzero
    intro hz_ne
    rw [h_fz_eq]
    apply mul_ne_zero
    · apply pow_ne_zero
      exact sub_ne_zero.mpr hz_ne
    · exact h_σz_nonzero

  have h_eventually_not_in_zeroset : ∀ᶠ z in nhds σ, z ≠ σ → z ∉ zerosetKfR R1 (by linarith) f := by
    filter_upwards [h_f_eventually_nonzero] with z h_fz_nonzero
    intro hz_ne hz_in_zeroset
    exact h_fz_nonzero hz_ne hz_in_zeroset.2

  filter_upwards [h_f_eq, h_eventually_not_in_zeroset] with z h_fz_eq h_not_in_zeroset
  intro hz_ne
                                                                    
  have hz_not_in_K : z ∉ zerosetKfR R1 (by linarith) f := h_not_in_zeroset hz_ne
                                                       
  unfold Cf
  simp [hz_not_in_K, h_fz_eq]

lemma lem_prod_no_sigma1
    {R R1 : ℝ} {hR1_pos : 0 < R1} {_hR1_lt_R : R1 < R} {_hR_lt_1 : R < 1}
    {f : ℂ → ℂ} {_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z} {_h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) (z : ℂ) :
    ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat =
    (z - σ) ^ (analyticOrderAt f σ).toNat *
    ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
  classical
  have hmem : σ ∈ h_finite_zeros.toFinset :=
    (Set.Finite.mem_toFinset (hs := h_finite_zeros)).2 hσ
  simpa using
    (Finset.mul_prod_erase (s := h_finite_zeros.toFinset)
      (f := fun ρ => (z - ρ) ^ (analyticOrderAt f ρ).toNat) (a := σ) hmem).symm

lemma lem_Cf_at_sigma_offK
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∀ᶠ z in nhds σ, z ≠ σ →
      Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      h_σ σ z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
                                            
  have h_cf_form := @lem_Cf_at_sigma_offK0 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec σ hσ

  filter_upwards [h_cf_form] with z h_cf_z
  intro hz_ne_sigma
                                              
  rw [h_cf_z hz_ne_sigma]
                                                 
  have h_prod_decomp := @lem_prod_no_sigma1 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros σ hσ z
                                                                            
  rw [h_prod_decomp]
                                                                  
  apply mul_div_mul_left
                       
  apply pow_ne_zero
  exact sub_ne_zero.mpr hz_ne_sigma

lemma lem_Cf_at_sigma
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∀ᶠ z in nhds σ,
      Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      h_σ σ z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
                                                 
  have h_on := @lem_Cf_at_sigma_onK R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec σ hσ
  have h_off := @lem_Cf_at_sigma_offK R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec σ hσ
                                      
  filter_upwards [h_on, h_off] with z hz_on hz_off
  by_cases h : z = σ
  ·                                                                
    have eq_result := hz_on h
                                                                  
    rw [h] at eq_result ⊢
    exact eq_result
  ·                                  
    exact hz_off h

lemma lem_h_ratio_anal
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (σ : ℂ) (_hσ : σ ∈ zerosetKfR R1 (by linarith) f)
    (g : ℂ → ℂ) (hg_analytic : AnalyticAt ℂ g σ) :
    AnalyticAt ℂ
      (fun z => g z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ),
        (z - ρ) ^ (analyticOrderAt f ρ).toNat) σ := by
                                                                             
  have hden := lem_denomAnalAt (S := h_finite_zeros.toFinset.erase σ)
    (n := fun ρ => (analyticOrderAt f ρ).toNat)
    (_hn_pos := by
      intro s hs
      have h_s_in_zeros : s ∈ zerosetKfR R1 (by linarith) f := by
        have h_mem_erase : s ∈ h_finite_zeros.toFinset.erase σ := hs
        have h_mem_orig : s ∈ h_finite_zeros.toFinset := Finset.mem_of_mem_erase h_mem_erase
        exact h_finite_zeros.mem_toFinset.mp h_mem_orig
      have h_order_ge_1 := lem_m_rho_ge_1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 s h_s_in_zeros
      have h_order_finite := lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 s h_s_in_zeros
      cases' h_cases : analyticOrderAt f s with n
      ·                    
        rw [h_cases] at h_order_finite
        exact False.elim (h_order_finite rfl)
      ·                               
        have n_ge_1 : n ≥ 1 := by
          rw [h_cases] at h_order_ge_1
          exact Nat.cast_le.mp h_order_ge_1
        simp
        exact Nat.pos_iff_ne_zero.mpr (ne_of_gt n_ge_1))
    (w := σ)
    (hw := by
      simp [Finset.mem_erase])
                                                   
  exact AnalyticAt.div hg_analytic hden.1 hden.2

lemma lem_Cf_analytic_at_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    AnalyticAt ℂ (Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) σ := by
                                                                               
  have h_eventually_eq := @lem_Cf_at_sigma R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec σ hσ

  obtain ⟨h_σ_analytic, _, _⟩ := h_σ_spec σ hσ
  have h_ratio_analytic := @lem_h_ratio_anal R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros σ hσ (h_σ σ) h_σ_analytic

  have h_rev_eq : (fun z => h_σ σ z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat) =ᶠ[nhds σ]
                  (Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) := by
    filter_upwards [h_eventually_eq] with z h_z
    exact h_z.symm

  exact AnalyticAt.congr h_ratio_analytic h_rev_eq

lemma lem_f_nonzero_off_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {_hR1_lt_R : R1 < R} {_hR_lt_1 : R < 1}
    {f : ℂ → ℂ} {_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z} {_h_f_nonzero_at_zero : f 0 ≠ 0}
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f) :
    f z ≠ 0 := by
  exact fun h => hz.2 ⟨hz.1, h⟩

lemma lem_Cf_nonzero_off_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (_h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f) :
    Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z ≠ 0 := by
                                                     
  have hz_not_in : z ∉ zerosetKfR R1 (by linarith) f := hz.2

  have h_cf_eq : Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
    f z / ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
    unfold Cf
    simp [hz_not_in]

  rw [h_cf_eq]

  apply div_ne_zero

  · apply @lem_f_nonzero_off_K R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero z hz

  · apply Finset.prod_ne_zero_iff.mpr
    intro ρ hρ
                                                     
    apply pow_ne_zero
                                  
    intro h_eq
                                                            
    have hz_eq_rho : z = ρ := by
      rwa [sub_eq_zero] at h_eq
                                                                             
    have hρ_in : ρ ∈ zerosetKfR R1 (by linarith) f := h_finite_zeros.mem_toFinset.mp hρ
    rw [hz_eq_rho] at hz_not_in
    exact hz_not_in hρ_in

lemma lem_Cf_nonzero_on_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ σ ≠ 0 := by
  have hnum : h_σ σ σ ≠ 0 := (h_σ_spec σ hσ).2.1
  have hden :
      (∏ ρ ∈ (h_finite_zeros.toFinset.erase σ),
        (σ - ρ) ^ (analyticOrderAt f ρ).toNat) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro ρ hρmem
    have hρ_ne_σ : ρ ≠ σ := (Finset.mem_erase.mp hρmem).1
    have hσ_ne_ρ : σ ≠ ρ := hρ_ne_σ.symm
    exact pow_ne_zero _ (sub_ne_zero.mpr hσ_ne_ρ)
  have :
      h_σ σ σ /
          ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ),
            (σ - ρ) ^ (analyticOrderAt f ρ).toNat ≠
        0 := by
    exact div_ne_zero hnum hden
  simpa [Cf, hσ] using this

lemma lem_Cf_never_zero
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R1) :
    Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z ≠ 0 := by
                                                         
  by_cases h : z ∈ zerosetKfR R1 (by linarith) f
  ·                                           
    exact lem_Cf_nonzero_on_K h_finite_zeros h_σ h_σ_spec z h
  ·                                           
    have hz_diff : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f := ⟨hz, h⟩
    exact lem_Cf_nonzero_off_K h_finite_zeros h_σ h_σ_spec z hz_diff

noncomputable def Bf
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (z : ℂ) : ℂ :=
  Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z *
  ∏ ρ ∈ h_finite_zeros.toFinset,
    ((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat

lemma lem_finset_prod_analyticAt {α : Type*} {S : Finset α} {g : α → ℂ → ℂ} (w : ℂ) :
  (∀ a ∈ S, AnalyticAt ℂ (g a) w) → AnalyticAt ℂ (fun z => ∏ a ∈ S, g a z) w := by
  intro h
  classical
  induction S using Finset.induction with
  | empty =>
                                                                
    simp only [Finset.prod_empty]
    exact analyticAt_const
  | insert a s ha ih =>
                                                     
    simp only [Finset.prod_insert ha]
                                               
    apply AnalyticAt.fun_mul
    ·                        
      apply h
      exact Finset.mem_insert_self a s
    ·                                                           
      apply ih
      intro b hb
      apply h
      exact Finset.mem_insert_of_mem hb

theorem lem_Bf_is_analytic (R R1 : ℝ) (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    AnalyticOnNhd ℂ (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) (Metric.closedBall (0 : ℂ) R) := by
                                   
  intro z hz

  have h_blaschke_linear : ∀ ρ ∈ h_finite_zeros.toFinset,
    AnalyticAt ℂ (fun w => (R : ℂ) - star ρ * w / (R : ℂ)) z := by
    intro ρ hρ
                                         
    have h_eq : (fun w : ℂ => (R : ℂ) - star ρ * w / (R : ℂ)) =
                (fun w : ℂ => (R : ℂ) + (-(star ρ) / (R : ℂ)) * w) := by
      funext w
      field_simp
      ring
    rw [h_eq]
    exact analyticAt_const.add (analyticAt_const.mul analyticAt_id)

  have h_powers : ∀ ρ ∈ h_finite_zeros.toFinset,
    AnalyticAt ℂ (fun w => ((R : ℂ) - star ρ * w / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) z := by
    intro ρ hρ
    exact (h_blaschke_linear ρ hρ).fun_pow _

  have h_product : AnalyticAt ℂ (fun w => ∏ ρ ∈ h_finite_zeros.toFinset,
      ((R : ℂ) - star ρ * w / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) z := by
                                                                       
    apply lem_finset_prod_analyticAt z
    intro ρ hρ
    apply h_powers
    exact hρ
                                                             
  by_cases hz_in : z ∈ zerosetKfR R1 (by linarith) f
  ·                                                                                 
    have h_cf_at_sigma := @lem_Cf_analytic_at_K R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz_in
                                                                          
    exact AnalyticAt.fun_mul h_cf_at_sigma h_product

  ·                                                    
    have hz_in_compl : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 (by linarith) f := by
      constructor
      · exact hz
      · exact hz_in
    have h_cf_off := @lem_Cf_analytic_off_K R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz_in_compl
    exact AnalyticAt.fun_mul h_cf_off h_product

variable {R R1 r B : ℝ} {f : ℂ → ℂ} {h_σ : ℂ → (ℂ → ℂ)}
variable (hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
variable (hR1_pos : 0 < R1)
variable (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
variable (h_f_zero : f 0 = 1)
variable (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
variable (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)

lemma f_zero_ne_zero (h_f_zero : f 0 = 1) : f 0 ≠ 0 := by
  rw [h_f_zero]; simp

lemma Bf_is_analytic_on_disk
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    AnalyticOnNhd ℂ (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ) (Metric.closedBall (0 : ℂ) R) :=
    let hspec := h_σ_spec
    lem_Bf_is_analytic R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero)
      h_finite_zeros h_σ hspec

lemma lem_Bf_eq_prod_Cf
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (_h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z, Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      (∏ ρ ∈ h_finite_zeros.toFinset,
        ((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) *
      (Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z) := by
  intro z
  rw [Bf]
  ring

lemma lem_num_prod_never_zero_all
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (_hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (_h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1,
      (∏ ρ ∈ h_finite_zeros.toFinset,
        ((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) ≠ 0 := by
  intro z hz
  apply Finset.prod_ne_zero_iff.mpr
  intro ρ hρ
  apply pow_ne_zero

  have hρ_mem : ρ ∈ zerosetKfR R1 (by linarith) f := by
    rwa [Set.Finite.mem_toFinset h_finite_zeros] at hρ
  have hρ_bound : ‖ρ‖ ≤ R1 := by
    rw [zerosetKfR] at hρ_mem; simp at hρ_mem; exact hρ_mem.1
  have hz_bound : ‖z‖ ≤ R1 := by
    rw [Metric.mem_closedBall, dist_zero_right] at hz; exact hz

  have hR_pos : (0 : ℝ) < R := lt_trans hR1_pos hR1_lt_R

  have key_positive : (0 : ℝ) < R - R1 * R1 / R := by
                                                  
    have h1 : R1 * R1 < R * R := by
      apply mul_self_lt_mul_self (le_of_lt hR1_pos) hR1_lt_R
    have h2 : R1 * R1 / R < R := by
      rw [div_lt_iff₀ hR_pos]
      exact h1
    linarith [h2]

  suffices h : (0 : ℝ) < ‖(R : ℂ) - star ρ * z / (R : ℂ)‖ by
    exact norm_pos_iff.mp h

  have triangle_ineq : ‖(R : ℂ) - star ρ * z / (R : ℂ)‖ ≥ ‖(R : ℂ)‖ - ‖star ρ * z / (R : ℂ)‖ :=
    norm_sub_norm_le _ _

  have R_norm_eq : ‖(R : ℂ)‖ = R := by
    rw [Complex.norm_of_nonneg (le_of_lt hR_pos)]

  have product_bound : ‖star ρ * z / (R : ℂ)‖ ≤ R1 * R1 / R := by
    rw [norm_div, norm_mul, norm_star, R_norm_eq]

    have mult_bound : ‖ρ‖ * ‖z‖ ≤ R1 * R1 := by
      exact mul_le_mul hρ_bound hz_bound (norm_nonneg _) (le_of_lt hR1_pos)
                                                                                
    have : ‖ρ‖ * ‖z‖ / R ≤ R1 * R1 / R := by
      exact div_le_div_of_nonneg_right mult_bound (le_of_lt hR_pos)
    exact this

  rw [R_norm_eq] at triangle_ineq
  linarith [triangle_ineq, product_bound, key_positive]

lemma Bf_never_zero
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1, Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z ≠ 0 := by
  intro z hz
                                                               
  rw [lem_Bf_eq_prod_Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ h_σ_spec]
                                                                  
  apply mul_ne_zero
  ·                                                                                  
    exact lem_num_prod_never_zero_all R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ h_σ_spec z hz
  ·                                                       
    exact lem_Cf_never_zero h_finite_zeros h_σ h_σ_spec z hz

noncomputable def Lf : ℂ → ℂ :=
  let B_f := Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ
  Classical.choose (log_of_analytic
    (r1 := r) (R' := R1) (R := R)
    hr_pos hr_lt_R1 hR1_lt_R hR_lt_1
    (B := B_f)
    (hB := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
    (hB_ne_zero := by
      intro z hz
      have h_num_ne_zero : B_f z ≠ 0 :=
        Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz
      assumption
    )
)

lemma Lf_is_analytic
    (r R R1 : ℝ)
    (hr_pos : 0 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    AnalyticOnNhd ℂ (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec)
                     (Metric.closedBall (0 : ℂ) r) := by
  unfold Lf
  exact (Classical.choose_spec (log_of_analytic
    (r1 := r) (R' := R1) (R := R)
    hr_pos hr_lt_R1 hR1_lt_R hR_lt_1
    (B := Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ)
    (hB := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
    (hB_ne_zero := by
      intro z hz
      exact Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz
    )
  )).1

lemma Lf_at_0_is_0
    (r R R1 : ℝ)
    (hr_pos : 0 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec 0 = 0 := by
  unfold Lf
  let B_f := Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ
  let log_exists := log_of_analytic
    (r1 := r) (R' := R1) (R := R)
    hr_pos hr_lt_R1 hR1_lt_R hR_lt_1
    (B := B_f)
    (hB := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
    (hB_ne_zero := by
      intro z hz
      have h_num_ne_zero : B_f z ≠ 0 :=
        Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz
      assumption
    )
  exact (Classical.choose_spec log_exists).2.1

lemma logDerivconst {a : ℂ} {g : ℂ → ℂ} (ha : a ≠ 0) :
    ∀ z, logDeriv (fun w ↦ a * g w) z = logDeriv g z := by
  intro z
  exact logDeriv_const_mul z a ha

lemma Lf_deriv_is_logBf_deriv (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
      logDeriv (fun w ↦ Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w /
                           Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0) z =
      logDeriv (fun w ↦ Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w) z := by
  intro z _
                                                      
  have h_eq : (fun w ↦ Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w /
                       Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0) =
              (fun w ↦ (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0)⁻¹ *
                       Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w) := by
    ext w
    rw [div_eq_mul_inv]
    ring
  rw [h_eq]
                                               
  have h0_in_ball : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R1 := by
    simp [Metric.mem_closedBall]
    exact le_of_lt hR1_pos
  have h_Bf0_ne_zero := Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec 0 h0_in_ball
                                      
  have h_inv_ne_zero : (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0)⁻¹ ≠ 0 :=
    inv_ne_zero h_Bf0_ne_zero
                        
  exact logDerivconst h_inv_ne_zero z

lemma deriv_over_fun_is_logDeriv {g : ℂ → ℂ} : ∀ z, deriv g z / g z = logDeriv g z := by
  intro z
  rfl

lemma logDerivmul {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z)
    (hf_ne : f z ≠ 0) (hg_ne : g z ≠ 0) :
    logDeriv (fun w ↦ f w * g w) z = logDeriv f z + logDeriv g z := by
  exact logDeriv_mul z hf_ne hg_ne hf hg

lemma logDerivprod {K : Finset ℂ} {g : ℂ → ℂ → ℂ} {z : ℂ}
    (hg_diff : ∀ ρ ∈ K, DifferentiableAt ℂ (g ρ) z)
    (hg_ne : ∀ ρ ∈ K, g ρ z ≠ 0) :
    logDeriv (fun w ↦ ∏ ρ ∈ K, g ρ w) z = ∑ ρ ∈ K, logDeriv (g ρ) z := by
  simpa only [Finset.prod_fn] using logDeriv_prod hg_ne hg_diff

lemma logDerivdiv {h g : ℂ → ℂ} {z : ℂ}
    (hh : DifferentiableAt ℂ h z) (hg : DifferentiableAt ℂ g z)
    (hh_ne : h z ≠ 0) (hg_ne : g z ≠ 0) :
    logDeriv (fun w ↦ h w / g w) z = logDeriv h z - logDeriv g z := by
  exact logDeriv_div z hh_ne hg_ne hh hg

lemma logDerivfunpow {g : ℂ → ℂ} {z : ℂ} {m : ℕ}
    (hg : DifferentiableAt ℂ g z) :
    logDeriv (fun w ↦ (g w) ^ m) z = m * logDeriv g z := by
  exact logDeriv_fun_pow hg m

lemma z_minus_rho_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (_hR1_lt_R : R1 < R) (_hR_lt_1 : R < 1)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_h_f_zero : f 0 = 1)
    (_h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    z - ρ ≠ 0 ∧ DifferentiableAt ℂ (fun w ↦ w - ρ) z := by
  intro ρ hρ z hz
  have hz_pair := (Set.mem_sdiff z).1 hz
  have hz_ball : z ∈ Metric.closedBall (0 : ℂ) R1 := hz_pair.1
  have hz_notK : z ∉ zerosetKfR R1 (by linarith) f := hz_pair.2
                               
  have hz_ne_rho : z ≠ ρ := by
    intro h_eq
    exact hz_notK (by simpa [h_eq] using hρ)
  have h_nonzero : z - ρ ≠ 0 := sub_ne_zero.mpr hz_ne_rho
                                        
  have hdiff : DifferentiableAt ℂ (fun w => w) z := differentiableAt_fun_id
  have hdiff_sub : DifferentiableAt ℂ (fun w => w - ρ) z := hdiff.sub_const ρ
  exact ⟨h_nonzero, hdiff_sub⟩

lemma blaschke_num_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (_hR_lt_1 : R < 1)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_h_f_zero : f 0 = 1)
    (_h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R,
    R - (star ρ) * z / R ≠ 0 ∧ DifferentiableAt ℂ (fun w ↦ R - (star ρ) * w / R) z := by
  intro ρ hρ z hz
  constructor
  · intro hzero
    have hRne : (R : ℂ) ≠ 0 := by
      simpa using (Complex.ofReal_ne_zero.mpr (ne_of_gt (hR1_pos.trans hR1_lt_R)))
                                                                          
    have heq : (R : ℂ) = (star ρ) * z / (R : ℂ) := sub_eq_zero.mp hzero
    have hmul := congrArg (fun t : ℂ => t * (R : ℂ)) heq
    have heq_mul : (R : ℂ) * (R : ℂ) = (star ρ) * z := by
                                     
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hRne] using hmul
                              
    have hnorm_eq : ‖(R : ℂ)‖ * ‖(R : ℂ)‖ = ‖ρ‖ * ‖z‖ := by
      simpa [Complex.norm_mul, Complex.norm_conj] using congrArg (fun t : ℂ => ‖t‖) heq_mul
                                   
    have hz_norm_le : ‖z‖ ≤ R := by
      have hz' : dist z (0 : ℂ) ≤ R := (Metric.mem_closedBall.mp hz)
      simpa [dist_eq_norm] using hz'
    have hrho_norm_le : ‖ρ‖ ≤ R1 := by
      rcases hρ with ⟨hρ_ball, _hρ_zero⟩
      have : dist ρ (0 : ℂ) ≤ R1 := (Metric.mem_closedBall.mp hρ_ball)
      simpa [dist_eq_norm] using this
    have hz_nonneg : 0 ≤ ‖z‖ := by simp
    have hR1_nonneg : 0 ≤ R1 := le_of_lt hR1_pos
    have hle : ‖ρ‖ * ‖z‖ ≤ R1 * R := by
      have h1 : ‖ρ‖ * ‖z‖ ≤ R1 * ‖z‖ := mul_le_mul_of_nonneg_right hrho_norm_le hz_nonneg
      have h2 : R1 * ‖z‖ ≤ R1 * R := mul_le_mul_of_nonneg_left hz_norm_le hR1_nonneg
      exact le_trans h1 h2
                                            
    have hnorm_R : ‖(R : ℂ)‖ = R := by
      have h1 : ‖(R : ℂ)‖ = |R| := by simp
      simp [abs_of_pos (hR1_pos.trans hR1_lt_R)]
                                         
    have : R * R = ‖ρ‖ * ‖z‖ := by simpa [hnorm_R] using hnorm_eq
    have hle' : R * R ≤ R1 * R := by simpa [this] using hle
                                                                     
    have hposR : 0 < R := hR1_pos.trans hR1_lt_R
    have hposRR : 0 < R * R := by nlinarith [hposR]
    have hlt : R1 * R < R * R := by
      exact mul_lt_mul_of_pos_right hR1_lt_R hposR
    exact (lt_irrefl _ (lt_of_le_of_lt hle' hlt))
  ·                                      
    have h_const : DifferentiableAt ℂ (fun _ : ℂ => (R : ℂ)) z := by
      simp
    have h_id : DifferentiableAt ℂ (fun w : ℂ => w) z := by
      simp
    have h_mul : DifferentiableAt ℂ (fun w : ℂ => (star ρ) * w) z := by
      simpa using h_id.const_mul (star ρ)
    have h_div : DifferentiableAt ℂ (fun w : ℂ => (star ρ) * w / (R : ℂ)) z := by
      simpa [div_eq_mul_inv] using h_mul.mul_const ((R : ℂ)⁻¹)
    simpa using h_const.sub h_div

lemma blaschke_frac_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    (R - (star ρ) * z / R) / (z - ρ) ≠ 0 ∧
    DifferentiableAt ℂ (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro ρ hρ z hz
                                                 
  have hden := z_minus_rho_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ z hz
  have hden_ne : z - ρ ≠ 0 := hden.1
  have hden_diff : DifferentiableAt ℂ (fun w ↦ w - ρ) z := hden.2
                                                  
  have hz_in_small : z ∈ Metric.closedBall (0 : ℂ) R1 ∧
      z ∉ zerosetKfR R1 (by linarith) f := by
    simpa [Set.mem_sdiff] using hz
  have hz_small : z ∈ Metric.closedBall (0 : ℂ) R1 := hz_in_small.1
                                                       
  have hz_dist_le_small : dist z (0 : ℂ) ≤ R1 := by
    simpa [Metric.mem_closedBall] using hz_small
  have hRle : R ≤ 1 := le_of_lt hR_lt_1
  have hR1_le_R : R1 ≤ R := le_of_lt hR1_lt_R
  have hR1_le_1 : R1 ≤ 1 := le_trans hR1_le_R hRle
  have hz_ball1 : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    have hz_le1 : dist z (0 : ℂ) ≤ 1 := le_trans hz_dist_le_small hR1_le_1
    simpa [Metric.mem_closedBall] using hz_le1
                                               
  have hz_ballR : z ∈ Metric.closedBall (0 : ℂ) R := by
    have hz_le_R : dist z (0 : ℂ) ≤ R := le_trans hz_dist_le_small (le_of_lt hR1_lt_R)
    simpa [Metric.mem_closedBall] using hz_le_R
  have hnum := blaschke_num_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ z hz_ballR
  have hnum_ne : R - (star ρ) * z / R ≠ 0 := hnum.1
  have hnum_diff : DifferentiableAt ℂ (fun w ↦ R - (star ρ) * w / R) z := hnum.2
             
  refine And.intro ?_ ?_
  · intro h
    have h' : (R - (star ρ) * z / R) * (z - ρ)⁻¹ = 0 := by
      simpa [div_eq_mul_inv] using h
    rcases mul_eq_zero.mp h' with hnum0 | hinv0
    · exact hnum_ne hnum0
    · exact hden_ne (inv_eq_zero.mp hinv0)
  · exact hnum_diff.div hden_diff hden_ne

lemma blaschke_pow_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    ((R - (star ρ) * z / R) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat ≠ 0 ∧
    DifferentiableAt ℂ (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro ρ hρ z hz
  have hfrac :=
    blaschke_frac_diff_nonzero (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros
      ρ hρ z hz
  rcases hfrac with ⟨hne, hdiff⟩
  constructor
  · exact pow_ne_zero _ hne
  · convert (preTransparency := .instances) hdiff.pow ((analyticOrderAt f ρ).toNat) using 1
    all_goals try with_reducible_and_instances rfl

lemma blaschke_prod_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    (∏ ρ ∈ h_finite_zeros.toFinset, ((R - (star ρ) * z / R) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat) ≠ 0 ∧
    DifferentiableAt ℂ (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
                        ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro z hz
  classical
  constructor
  ·                                
    have hne_each : ∀ ρ ∈ h_finite_zeros.toFinset,
        ((R - (star ρ) * z / R) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat ≠ 0 := by
      intro ρ hρ
      have hρ' : ρ ∈ zerosetKfR R1 (by linarith) f :=
        (h_finite_zeros.mem_toFinset).1 hρ
      have hpair :=
        blaschke_pow_diff_nonzero (R := R) (R1 := R1) (f := f)
          hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ' z hz
      exact hpair.1
    exact (Finset.prod_ne_zero_iff).2 hne_each
  ·                                    
    have hdiff_each : ∀ ρ ∈ h_finite_zeros.toFinset,
        DifferentiableAt ℂ
          (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
      intro ρ hρ
      have hρ' : ρ ∈ zerosetKfR R1 (by linarith) f :=
        (h_finite_zeros.mem_toFinset).1 hρ
      have hpair :=
        blaschke_pow_diff_nonzero (R := R) (R1 := R1) (f := f)
          hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ' z hz
      exact hpair.2
                                                                 
    have hdiff :=
      (DifferentiableAt.finsetProd (u := h_finite_zeros.toFinset)
        (f := fun ρ => fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat)
        (x := z) hdiff_each)
    have hfun_eq :
        (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
            ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat)
        =
        (∏ ρ ∈ h_finite_zeros.toFinset,
            (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat)) := by
      funext w
      simp [Finset.prod_apply]
    exact hfun_eq.symm ▸ hdiff

lemma f_diff_nonzero_outside_Kf {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_h_f_zero : f 0 = 1)
    (_h_finite_zeros : (zerosetKfR R1 (by linarith ) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    f z ≠ 0 ∧ DifferentiableAt ℂ f z := by
  intro z hz
                                            
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R1 ∧
      z ∉ zerosetKfR R1 (by linarith) f := by
    simpa [Set.mem_sdiff] using hz
  have hz_in_R1 : z ∈ Metric.closedBall (0 : ℂ) R1 := hz'.1
  have hz_notin : z ∉ zerosetKfR R1 (by linarith) f := hz'.2
                 
  have hz_nonzero : f z ≠ 0 := by
    intro hfz
    exact hz_notin ⟨hz_in_R1, hfz⟩
                                                               
  have hR1_lt_1 : R1 < 1 := by linarith
  have hsubset1 :
      Metric.closedBall (0 : ℂ) R1 ⊆ Metric.ball (0 : ℂ) 1 :=
    Metric.closedBall_subset_ball hR1_lt_1
  have hz_in_ball1 : z ∈ Metric.ball (0 : ℂ) 1 := hsubset1 hz_in_R1
  have hz_in_1 : z ∈ Metric.closedBall (0 : ℂ) 1 :=
    Metric.ball_subset_closedBall hz_in_ball1
  have hAna : AnalyticAt ℂ f z := h_f_analytic z hz_in_1
  have hDiff : DifferentiableAt ℂ f z := hAna.differentiableAt
  exact ⟨hz_nonzero, hDiff⟩

lemma logDeriv_fprod_is_sum {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    logDeriv (fun w ↦ f w * ∏ ρ ∈ h_finite_zeros.toFinset,
             ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z =
    logDeriv f z + logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
                            ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro z hz
  have hf' := f_diff_nonzero_outside_Kf (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz
  rcases hf' with ⟨hf_ne, hf_diff⟩
  have hg' := blaschke_prod_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz
  rcases hg' with ⟨hg_ne, hg_diff⟩
  simpa using
    (logDerivmul (f:=f) (g:=fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
        ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) (z:=z)
      hf_diff hg_diff hf_ne hg_ne)

lemma div_mul_eq_mul_mul_inv_fun {α} (f A B : α → ℂ) :
  (fun w => (f w / A w) * B w) = (fun w => f w * (B w * (A w)⁻¹)) := by
  funext w
  simp [div_eq_mul_inv, mul_comm, mul_left_comm]

lemma prod_num_mul_inv_den_eq_prod_ratio_fun_mem
  (K : Finset ℂ) (N D : ℂ → ℂ → ℂ) (m : ℂ → ℕ) :
  (fun w ↦ (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) * (∏ ρ ∈ K, (D ρ w) ^ (m ρ))⁻¹)
  = (fun w ↦ ∏ ρ ∈ K, ((N ρ w / D ρ w) ^ (m ρ))) := by
  funext w
  classical
  calc
    (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) * (∏ ρ ∈ K, (D ρ w) ^ (m ρ))⁻¹
        = (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) / (∏ ρ ∈ K, (D ρ w) ^ (m ρ)) := by
          simp [div_eq_mul_inv]
    _ = ∏ ρ ∈ K, ((N ρ w) ^ (m ρ) / (D ρ w) ^ (m ρ)) := by
          simp
    _ = ∏ ρ ∈ K, ((N ρ w / D ρ w) ^ (m ρ)) := by
          refine Finset.prod_congr rfl ?_
          intro ρ hρ
          have hpow_div :
              (N ρ w / D ρ w) ^ (m ρ)
                = (N ρ w) ^ (m ρ) / (D ρ w) ^ (m ρ) := by
            calc
              (N ρ w / D ρ w) ^ (m ρ)
                  = (N ρ w * (D ρ w)⁻¹) ^ (m ρ) := by
                        simp [div_eq_mul_inv]
              _ = (N ρ w) ^ (m ρ) * ((D ρ w)⁻¹) ^ (m ρ) := by
                        simpa using (mul_pow (N ρ w) ((D ρ w)⁻¹) (m ρ))
              _ = (N ρ w) ^ (m ρ) * ((D ρ w) ^ (m ρ))⁻¹ := by
                        simp
              _ = (N ρ w) ^ (m ρ) / (D ρ w) ^ (m ρ) := by
                        simp [div_eq_mul_inv]
          simpa using hpow_div.symm

lemma logDeriv_congr_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ}
  (hfg : f =ᶠ[nhds z] g) : logDeriv f z = logDeriv g z := by
                                                                                         
  have hval : f z = g z := Filter.EventuallyEq.eq_of_nhds hfg
  have hderiv_eq_ev : deriv f =ᶠ[nhds z] deriv g := hfg.deriv
  have hderiv : deriv f z = deriv g z := Filter.EventuallyEq.eq_of_nhds hderiv_eq_ev
                                                      
  have hf := deriv_over_fun_is_logDeriv (g := f) z
  have hg := deriv_over_fun_is_logDeriv (g := g) z
  simp [hf.symm, hg.symm, hval, hderiv]

lemma logDeriv_Bf_is_sum :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \
          zerosetKfR R1 (by linarith) f,
    logDeriv (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ) z =
    logDeriv f z +
      logDeriv
        (fun w ↦
          ∏ ρ ∈ h_finite_zeros.toFinset,
            ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  classical
  intro z hz
                  
  set K : Finset ℂ := h_finite_zeros.toFinset
                                                                    
  let A : ℂ → ℂ := fun w => ∏ ρ ∈ K, (w - ρ) ^ (analyticOrderAt f ρ).toNat
  let BN : ℂ → ℂ := fun w => ∏ ρ ∈ K, (R - (star ρ) * w / R) ^ (analyticOrderAt f ρ).toNat
  let RatProd : ℂ → ℂ :=
    fun w => ∏ ρ ∈ K, ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat
                                                                              
  set S : Set ℂ := zerosetKfR R1 (by linarith) f
  have hS_fin : S.Finite := h_finite_zeros
  have hU_open : IsOpen Sᶜ := hS_fin.isClosed.isOpen_compl
  have hz_notin : z ∉ S := by
    rcases hz with ⟨_, hnotin⟩; exact hnotin
  have hzU : z ∈ Sᶜ := by simpa [Set.mem_compl] using hz_notin
  have hU_mem : Sᶜ ∈ nhds z := hU_open.mem_nhds hzU
  have h_ev :
      (fun w ↦ Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w)
        =ᶠ[nhds z]
      (fun w ↦ f w * RatProd w) := by
    refine Filter.eventually_of_mem hU_mem ?_
    intro w hwU
    have hw_notin : w ∉ S := by simpa [Set.mem_compl] using hwU
                                                         
    have hBf_w :
        Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w
          = Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w * BN w := by
      simp [Bf, BN, K]
    have hCf_w :
        Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w
          = f w / A w := by
      simp [Cf, S, A, K, hw_notin]
                                                           
    have h_eq1 := div_mul_eq_mul_mul_inv_fun (f := f) (A := A) (B := BN)
    have h_eq1_w : (f w / A w) * BN w = f w * (BN w * (A w)⁻¹) := by
      simpa using congrArg (fun g : (ℂ → ℂ) => g w) h_eq1
    have h_eq2 :=
      prod_num_mul_inv_den_eq_prod_ratio_fun_mem
        (K := K)
        (N := fun ρ w ↦ (R - (star ρ) * w / R))
        (D := fun ρ w ↦ (w - ρ))
        (m := fun ρ ↦ (analyticOrderAt f ρ).toNat)
    have h_eq2_w : BN w * (A w)⁻¹ = RatProd w := by
      simpa [BN, A, RatProd] using congrArg (fun g : (ℂ → ℂ) => g w) h_eq2
                           
    calc
      Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w
          = (f w / A w) * BN w := by simpa [hCf_w] using hBf_w
      _ = f w * (BN w * (A w)⁻¹) := h_eq1_w
      _ = f w * RatProd w := by simp [h_eq2_w]
                                       
  have hlog_congr := logDeriv_congr_of_eventuallyEq (f := fun w ↦
      Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w)
      (g := fun w ↦ f w * RatProd w) (z := z) h_ev
                                  
  have hsum :=
    (logDeriv_fprod_is_sum (R:=R) (R1:=R1) (f:=f)
      hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz)
  simpa [RatProd, K] using hlog_congr.trans hsum

lemma logDeriv_def_as_frac {f : ℂ → ℂ} {z : ℂ}
    (_hf : DifferentiableAt ℂ f z) (_hf_ne : f z ≠ 0) :
    logDeriv f z = deriv f z / f z := by
  simp [logDeriv]

theorem ball_containment {r R1 : ℝ} (_hr_pos : 0 < r) (hr_lt_R1 : r < R1) (z : ℂ) (hz : z ∈ Metric.closedBall 0 r) : z ∈ Metric.closedBall 0 R1 := by
  simp at *
  exact le_trans hz (le_of_lt hr_lt_R1)

theorem in_r_minus_kf {R1 r : ℝ} {f : ℂ → ℂ}
  (hr_pos : 0 < r)
  (hr_lt_R1 : r < R1)
  (z : ℂ)
  (hz : z ∈ Metric.closedBall 0 r \ zerosetKfR R1 (by linarith) f) :
   z ∈ Metric.closedBall 0 R1 \ zerosetKfR R1 (by linarith) f := by
  obtain ⟨h1, h2⟩ := hz
  have : z ∈ Metric.closedBall 0 R1 := by
    apply ball_containment hr_pos hr_lt_R1 z h1
  constructor <;> assumption

lemma Lf_deriv_step1 :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
    deriv f z / f z + logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
                                ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro z hz
                                  
  have hz' : z ∈ Metric.closedBall (0 : ℂ) r ∧ z ∉ zerosetKfR R1 (by linarith) f := by
    simpa [Set.mem_sdiff] using hz
  have hz_ball : z ∈ Metric.closedBall (0 : ℂ) r := hz'.1
                               
  have hLf :=
    
    (Lf_deriv_is_logBf_deriv hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec
      z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)).symm
                                   
  have hsum :
      logDeriv (fun w ↦
        Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero)
          h_finite_zeros h_σ w) z =
      logDeriv f z +
        logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
            ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
    have h :=
      (logDeriv_Bf_is_sum (R := R) (R1 := R1) (r := r) (f := f) (h_σ := h_σ)
        hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros) z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)
    simpa using h
                                                                              
  obtain ⟨hf_ne, hfdiff⟩ :=
    f_diff_nonzero_outside_Kf (R := R) (R1 := R1) (f := f)
      hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)
  have hfrac : logDeriv f z = deriv f z / f z :=
    logDeriv_def_as_frac (f := f) (z := z) hfdiff hf_ne

  have hLf_eq_logDerivBf :
      deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
      logDeriv (fun w ↦
        Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero)
          h_finite_zeros h_σ w) z := by

    have hz_in_r : z ∈ Metric.closedBall (0 : ℂ) r := hz_ball
                                                               
    let B_f : ℂ → ℂ :=
      fun w => Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w
    let log_exists := log_of_analytic
      (r1 := r) (R' := R1) (R := R)
      hr_pos hr_lt_R1 hR1_lt_R hR_lt_1
      (B := B_f)
      (hB := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1
                f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
      (hB_ne_zero := by
        intro w hw
        exact Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1
          f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec w hw)
    have hderiv_all : ∀ w ∈ Metric.closedBall (0 : ℂ) r,
        deriv (Classical.choose log_exists) w = deriv B_f w / B_f w :=
      (Classical.choose_spec log_exists).2.2.1
    have hderiv_Lf :
        deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos
                    h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z
          = deriv B_f z / B_f z := by
                                                                            
      unfold Lf
                                                                                                       
      simpa using hderiv_all z hz_in_r
                                                  
    have h_as_log : deriv B_f z / B_f z = logDeriv B_f z :=
      deriv_over_fun_is_logDeriv (g := B_f) z
               
    simpa [B_f] using hderiv_Lf.trans h_as_log

  calc
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z
        = logDeriv (fun w ↦
            Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero)
              h_finite_zeros h_σ w) z := hLf_eq_logDerivBf
    _ = logDeriv f z +
          logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
              ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := hsum
    _ = deriv f z / f z +
          logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
              ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
            simp [hfrac]

lemma logDeriv_prod_is_sum {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
             ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z =
    ∑ ρ ∈ h_finite_zeros.toFinset, logDeriv (fun w ↦
              ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro z hz
  have hdiff : ∀ ρ ∈ h_finite_zeros.toFinset,
      DifferentiableAt ℂ (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
    intro ρ hρ
    have hρmem : ρ ∈ zerosetKfR R1 (by linarith) f :=
      (h_finite_zeros.mem_toFinset).mp hρ
    have h := blaschke_pow_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρmem z hz
    exact h.2
  have hne : ∀ ρ ∈ h_finite_zeros.toFinset,
      ((R - (star ρ) * z / R) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat ≠ 0 := by
    intro ρ hρ
    have hρmem : ρ ∈ zerosetKfR R1 (by linarith) f :=
      (h_finite_zeros.mem_toFinset).mp hρ
    have h := blaschke_pow_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρmem z hz
    exact h.1
  simpa using
    (logDerivprod (K := h_finite_zeros.toFinset)
      (g := fun ρ w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat)
      (z := z) hdiff hne)

lemma logDeriv_power_is_mul {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    ∀ ρ ∈ h_finite_zeros.toFinset,
    logDeriv (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z =
    (analyticOrderAt f ρ).toNat * logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro z hz ρ hρFin
  have hρmem : ρ ∈ zerosetKfR R1 (by linarith) f := by
    simpa using (h_finite_zeros.mem_toFinset.mp hρFin)
  have hfrac :=
    blaschke_frac_diff_nonzero (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros
      ρ hρmem z hz
  rcases hfrac with ⟨_hneq, hdiff⟩
  simpa using
    (logDerivfunpow (g := fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) (z := z)
      (m := (analyticOrderAt f ρ).toNat) hdiff)

lemma logDeriv_prod_is_sum_mul {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
             ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z =
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat *
                                    logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro z hz
  classical
  have hsum :=
    logDeriv_prod_is_sum (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz
  refine hsum.trans ?_
  refine Finset.sum_congr rfl ?_
  intro ρ hρ
  exact
    logDeriv_power_is_mul (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz ρ hρ

lemma Lf_deriv_step2 :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
    deriv f z / f z + ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat *
                                                       logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro z hz
  classical
  have h1 :=
    Lf_deriv_step1 hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz
  have hsum :=
    logDeriv_prod_is_sum_mul (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)
  have h2 := congrArg (fun t => deriv f z / f z + t) hsum
  exact h1.trans h2

lemma logDeriv_Blaschke_is_diff {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    ∀ ρ ∈ h_finite_zeros.toFinset,
    logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z =
    logDeriv (fun w ↦ R - (star ρ) * w / R) z - logDeriv (fun w ↦ w - ρ) z := by
  intro z hz ρ hρ
  have hρ_set : ρ ∈ zerosetKfR R1 (by linarith) f := by
    exact (Set.Finite.mem_toFinset (hs := h_finite_zeros) (a := ρ)).mp hρ
  rcases hz with ⟨hz_in, hz_notin⟩
  have hden := z_minus_rho_diff_nonzero hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros
      ρ hρ_set z ⟨hz_in, hz_notin⟩
  rcases hden with ⟨hden_nz, hden_diff⟩
  have hz_le : ‖z‖ ≤ R1 := by
    simpa [Metric.closedBall, dist_eq_norm] using hz_in
  have hle1 : R1 < 1 := by linarith [hR1_lt_R, hR_lt_1]
  have hz_in1 : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    have : ‖z‖ ≤ 1 := le_of_lt (hz_le.trans_lt hle1)
    simpa [Metric.closedBall, dist_eq_norm] using this
  have hz_inR : z ∈ Metric.closedBall (0 : ℂ) R := by
    have hz_le_R : ‖z‖ ≤ R := by
      calc ‖z‖ ≤ R1 := hz_le
      _ ≤  R := le_of_lt hR1_lt_R
    simpa [Metric.closedBall, dist_eq_norm] using hz_le_R
  have hnum := blaschke_num_diff_nonzero hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros
      ρ hρ_set z hz_inR
  rcases hnum with ⟨hnum_nz, hnum_diff⟩
  simpa using
    (logDerivdiv (hh := hnum_diff) (hg := hden_diff) (hh_ne := hnum_nz) (hg_ne := hden_nz))

lemma logDeriv_linear {a b : ℂ} {z : ℂ} (_ha : a ≠ 0) (_hz : z ≠ -b/a) :
    logDeriv (fun w ↦ a * w + b) z = a / (a * z + b) := by
                                 
  have h_id : HasDerivAt (fun w : ℂ => w) (1 : ℂ) z := hasDerivAt_id _
  have h_mul' : HasDerivAt (fun w : ℂ => a * w) a z := by
    simpa [one_mul] using (h_id.const_mul a)
  have h_deriv_mul : deriv (fun w : ℂ => a * w) z = a := h_mul'.deriv
                                
  simp [logDeriv]

lemma logDeriv_denominator {ρ : ℂ} {z : ℂ} (hz : z ≠ ρ) :
    logDeriv (fun w ↦ w - ρ) z = 1 / (z - ρ) := by
  have h :=
    logDeriv_linear (a := (1 : ℂ)) (b := -ρ) (z := z)
      (_ha := by simp)
      (_hz := by simpa using hz)
  simpa [one_mul, sub_eq_add_neg] using h

lemma logDeriv_numerator_pre {R : ℝ} {ρ : ℂ} {z : ℂ} :
    logDeriv (fun w ↦ R - (star ρ) * w / R) z = -(star ρ) / R / (R - (star ρ) * z / R) := by
  classical
                                                  
  let a : ℂ := -(star ρ) / (R : ℂ)
  let b : ℂ := (R : ℂ)
  have hlin : (fun w : ℂ ↦ (R : ℂ) - (star ρ) * w / (R : ℂ)) = (fun w : ℂ ↦ b + a * w) := by
    funext w
                         
    simp [a, b, sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm]
                                        
  have hderiv_add : deriv (fun w : ℂ => b + a * w) z =
      deriv (fun _ : ℂ => b) z + deriv (fun y : ℂ => a * y) z := by
    simp
  have hderiv_ab : deriv (fun w : ℂ => b + a * w) z = a := by
    simp [deriv_const, mul_comm]
                                                            
  simp [logDeriv, sub_eq_add_neg, div_eq_mul_inv,
         mul_comm, mul_left_comm, mul_assoc, add_comm]

lemma star_ne_zero_of_ne_zero {ρ : ℂ} (hρ : ρ ≠ 0) : star ρ ≠ 0 := by

  intro h
                                          
  have : ρ = 0 := (star_eq_zero).1 h
  exact hρ this

lemma field_identity_general {K : Type*} [Field K] {a b c : K} (ha : a ≠ 0) (hb : b ≠ 0) (_hden : a - c*b/a ≠ 0) : (-(b/a)) / (a - c*b/a) = (1 : K) / (c - a^2/b) := by
                                               
  have hmul : (-(a / b) : K) ≠ 0 := by
    have hdiv_ne : a / b ≠ 0 := div_ne_zero ha hb
    exact neg_ne_zero.mpr hdiv_ne
  have hnum : (-(b/a) * (-(a/b))) = (1 : K) := by
    calc
      (-(b/a) * (-(a/b))) = (b/a) * (a/b) := by simp
      _ = (b * a⁻¹) * (a * b⁻¹) := by simp [div_eq_mul_inv]
      _ = b * (a⁻¹ * (a * b⁻¹)) := by simp [mul_assoc]
      _ = b * ((a⁻¹ * a) * b⁻¹) := by simp [mul_assoc]
      _ = b * (1 * b⁻¹) := by simp [ha]
      _ = b * b⁻¹ := by simp
      _ = 1 := by simp [hb]
  have hOne : (b/a) * (a/b) = (1 : K) := by
    calc
      (b/a) * (a/b) = (b * a⁻¹) * (a * b⁻¹) := by simp [div_eq_mul_inv]
      _ = b * (a⁻¹ * (a * b⁻¹)) := by simp [mul_assoc]
      _ = b * ((a⁻¹ * a) * b⁻¹) := by simp [mul_assoc]
      _ = b * (1 * b⁻¹) := by simp [ha]
      _ = b * b⁻¹ := by simp
      _ = 1 := by simp [hb]
  have haab : a * (a / b) = a^2 / b := by
    simp [div_eq_mul_inv, pow_two, mul_assoc]
  have hcbab : (c * b / a) * (a / b) = c := by
    calc
      (c * b / a) * (a / b) = (c * (b / a)) * (a / b) := by simp [div_eq_mul_inv, mul_assoc]
      _ = c * ((b / a) * (a / b)) := by simp [mul_assoc]
      _ = c * 1 := by simp [hOne]
      _ = c := by simp
  have hdenom : ((a - c*b/a) * (-(a/b))) = c - a^2 / b := by
    calc
      ((a - c*b/a) * (-(a/b))) = -((a - c*b/a) * (a / b)) := by simp [mul_neg]
      _ = -(a * (a / b) - (c * b / a) * (a / b)) := by simp [sub_mul]
      _ = (c * b / a) * (a / b) - a * (a / b) := by simp [neg_sub]
      _ = c - a^2 / b := by simp [hcbab, haab]
  calc
    (-(b/a)) / (a - c*b/a)
        = (-(b/a) * (-(a/b))) / ((a - c*b/a) * (-(a/b))) := by
          simpa using
            (mul_div_mul_right (a := (-(b / a))) (b := (a - c * b / a)) (c := (-(a / b))) hmul).symm
    _ = 1 / ((a - c*b/a) * (-(a/b))) := by simp [hnum]
    _ = 1 / (c - a^2/b) := by simp [hdenom]

lemma complex_identity_from_field {R : ℝ} {ρ z : ℂ} (hR : R ≠ 0) (hρ : ρ ≠ 0) (hden : (R:ℂ) - (star ρ) * z / R ≠ 0) : (-(star ρ) / (R:ℂ)) / ((R:ℂ) - (star ρ) * z / R) = (1 : ℂ) / (z - (R:ℂ)^2 / (star ρ)) := by
  have ha : (R : ℂ) ≠ 0 := by simpa using (Complex.ofReal_ne_zero.mpr hR)
  have hb : star ρ ≠ 0 := star_ne_zero_of_ne_zero hρ
  have hden' : (R : ℂ) - z * (star ρ) / (R : ℂ) ≠ 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hden
  have h := field_identity_general (K := ℂ) (a := (R : ℂ)) (b := star ρ) (c := z) ha hb hden'
  simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using h

lemma logDeriv_numerator_rearranged {R : ℝ} {ρ z : ℂ} (hR : R ≠ 0) (hrho : ρ ≠ 0) (h_denom_ne_zero : (R : ℂ) - (star ρ) * z / R ≠ 0) : -(star ρ) / R / ((R : ℂ) - (star ρ) * z / R) = 1 / (z - (R : ℂ)^2 / (star ρ)) := by
  simpa using (complex_identity_from_field (R:=R) (ρ:=ρ) (z:=z) (hR:=hR) (hρ:=hrho) (hden:=h_denom_ne_zero))

lemma logDeriv_numerator {R : ℝ} {ρ : ℂ} {z : ℂ}
    (hR : R ≠ 0)
    (hrho : ρ ≠ 0)
    (h_denom_ne_zero : (R : ℂ) - (star ρ) * z / R ≠ 0):
    logDeriv (fun w ↦ R - (star ρ) * w / R) z = 1 / (z - R^2 / (star ρ)) := by
  rw [logDeriv_numerator_pre, logDeriv_numerator_rearranged]
  <;> assumption

lemma logDeriv_Blaschke_is_diff_frac {R R1 : ℝ} {f : ℂ → ℂ}
     (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1) (h_f_zero : f 0 = 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ h_finite_zeros.toFinset,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f , logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z =
         1 / (z - R^2 / (star ρ)) - 1 / (z - ρ) := by
  intro ρ hρ z hz
                                                                         
  have h_div := logDeriv_Blaschke_is_diff (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz ρ hρ
                                                                     
  have hρ_mem : ρ ∈ zerosetKfR R1 (by linarith) f := by
    exact (h_finite_zeros.mem_toFinset).mp hρ
  have hρ_ne_zero : ρ ≠ 0 := by
    intro h_eq
                                                            
    have : f 0 = 0 := by simpa [h_eq] using hρ_mem.2
    exact (zero_ne_one : (0 : ℂ) ≠ 1) (this.symm.trans h_f_zero)
  have hR_ne_zero : R ≠ 0 := ne_of_gt (hR1_pos.trans hR1_lt_R)
  have h_denom_ne_zero : (R : ℂ) - (star ρ) * z / R ≠ 0 := by
                                                  
    have hz_ball : z ∈ Metric.closedBall (0 : ℂ) R := by
      have hle : R1 < R := hR1_lt_R
      apply Metric.closedBall_subset_closedBall (le_of_lt hle)
      exact hz.1
    have h := blaschke_num_diff_nonzero hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ_mem z hz_ball
    exact h.1
  have h_num := logDeriv_numerator hR_ne_zero hρ_ne_zero h_denom_ne_zero
                                                        
  have hz_ne_rho : z ≠ ρ := by
    intro h_eq
    exact hz.2 (by simpa [h_eq] using hρ_mem)
  have h_den := logDeriv_denominator hz_ne_rho
                                
  rw [h_div, h_num, h_den]

lemma Lf_deriv_step3 :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
    deriv f z / f z + ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat * (1 / (z - R^2 / (star ρ)) - 1 / (z - ρ)) := by
  intro z hz
                                                          
  rw [Lf_deriv_step2 hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz]
  congr 1
  apply Finset.sum_congr rfl
  intro ρ hρ
  congr 1
  exact logDeriv_Blaschke_is_diff_frac hR1_pos hR1_lt_R hR_lt_1 h_f_zero h_f_analytic h_finite_zeros ρ hρ z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)

lemma sum_rearranged {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (_hR1_lt_R : R1 < R) (_hR_lt_1 : R < 1)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat *
                                    (1 / (z - R^2 / (star ρ)) - 1 / (z - ρ)) =
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ)) -
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ) := by
  intro z hz
  rw [← Finset.sum_sub_distrib]
  congr 1
  ext ρ
  rw [mul_sub, mul_one_div, mul_one_div]

lemma Lf_deriv_final_formula :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
    deriv f z / f z - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ) +
                      ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ)) := by
  intro z hz
                                                               
  rw [Lf_deriv_step3 hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz]
                                                  
  rw [sum_rearranged hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz]
                    
  ring

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.Erdos970_PNT3_RiemannZeta
attribute [-simp] _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970


open scoped BigOperators Topology
abbrev ℙ := Nat.Primes

lemma Re2s (s : ℂ) : (2 * s).re = 2 * s.re := by simp

lemma Re2sge1 (s : ℂ) (hs : 1 < s.re) : 1 < (2 * s).re := by
  rw [Re2s]
  linarith

lemma tendsto_finprod_coe_iff_tendsto_coe_finprod {i : Type*} (f : i → NNReal) (a : NNReal) :
  Filter.Tendsto (fun s => ∏ i ∈ s, (f i : ℝ)) Filter.atTop (𝓝 (a : ℝ)) ↔
  Filter.Tendsto ((fun x : NNReal => (x : ℝ)) ∘ (fun s => ∏ i ∈ s, f i)) Filter.atTop (𝓝 (a : ℝ)) := by
                                                                                           
  have h_comp : ((fun x : NNReal => (x : ℝ)) ∘ (fun s => ∏ i ∈ s, f i)) = (fun s => ↑(∏ i ∈ s, f i)) := by
    rfl
                                                                  
  have h_eq : (fun s => ∏ i ∈ s, (f i : ℝ)) = (fun s => ↑(∏ i ∈ s, f i)) := by
    ext s
    exact (NNReal.coe_prod s f).symm
                                                                   
  rw [h_comp, ← h_eq]

lemma pnt_nnreal_isEmbedding_coe : Topology.IsEmbedding (fun x : NNReal => (x : ℝ)) := by
  refine ⟨?_, NNReal.coe_injective⟩
                                                              
  exact Topology.IsInducing.subtypeVal

lemma HasProd.of_coe_hasProd {i : Type*} (f : i → NNReal) (a : NNReal) (h : HasProd (fun i => (f i : ℝ)) (a : ℝ)) : HasProd f a := by
                                                                                     
  have h_comp : Filter.Tendsto ((fun x : NNReal => (x : ℝ)) ∘ (fun s => ∏ i ∈ s, f i)) Filter.atTop (𝓝 (a : ℝ)) := by
    rw [← tendsto_finprod_coe_iff_tendsto_coe_finprod]
    exact h

  have h_embed : Topology.IsEmbedding (fun x : NNReal => (x : ℝ)) := pnt_nnreal_isEmbedding_coe

  exact h_embed.tendsto_nhds_iff.mpr h_comp

open _root_.Real _root_.Set _root_.Filter Topology _root_.MeasureTheory
open scoped BigOperators Topology

lemma T_eq_inter_S_half (S T : Set ℂ) (_hS : S = {s : ℂ | s ≠ 1}) (hT : T = {s : ℂ | s ∈ S ∧ (1/10 : ℝ) < s.re}) :
  T = S ∩ {s : ℂ | (1/10 : ℝ) < s.re} := by
  classical
  ext z
  simp [hT, Set.inter_def]

open Metric _root_.Set _root_.Filter Asymptotics BigOperators

noncomputable def logDerivZeta (s : ℂ) : ℂ := deriv riemannZeta s / riemannZeta s

def zerosetKfRc (R : ℝ) (c : ℂ) (f : ℂ → ℂ) : Set ℂ :=
  {ρ : ℂ | ρ ∈ Metric.closedBall c R ∧ f ρ = 0}

lemma DiffAtOn {T : Set ℂ} {g : ℂ → ℂ} :
    (∀ s ∈ T, DifferentiableAt ℂ g s) → DifferentiableOn ℂ g T := by
  intro h s hs
  exact (h s hs).differentiableWithinAt

lemma DiffOnanalOnNhd {T : Set ℂ} (hT : IsOpen T) {g : ℂ → ℂ} :
    DifferentiableOn ℂ g T → AnalyticOnNhd ℂ g T := by
  intro hdiff
  exact hdiff.analyticOnNhd hT

lemma DiffAtallanalOnNhd {T : Set ℂ} (hT : IsOpen T) {g : ℂ → ℂ} :
    (∀ s ∈ T, DifferentiableAt ℂ g s) → AnalyticOnNhd ℂ g T := by
  intro hdiff
  apply DiffOnanalOnNhd hT
  exact DiffAtOn hdiff

lemma I_mul_ofReal_im (t : ℝ) : (I * ↑t).im = t := by
  have h1 : (I * (↑t : ℂ)).im = (↑t : ℂ).re := Complex.I_mul_im (↑t : ℂ)
  rw [h1]
  simp [Complex.ofReal_re]

lemma complex_im_sub_I_mul (a : ℂ) (t : ℝ) : (a - I * t).im = a.im - t := by
  rw [Complex.sub_im]
  rw [I_mul_ofReal_im]

lemma D1cinTt_pre (t : ℝ) (ht : |t| > 1) :
    ∀ s ∈ closedBall (3/2 + I * t : ℂ) 1, s ≠ 1 := by
  intro s hs
  by_contra h
                                                   
  rw [h] at hs
                                            
  rw [mem_closedBall] at hs
                                  
  rw [Complex.dist_eq] at hs

  have h1 : (1 : ℂ) - (3/2 + I * t) = -1/2 - I * t := by ring
  rw [h1] at hs

  have h2 : (-1/2 - I * t : ℂ).im = -t := by
    have : (-1/2 - I * t : ℂ) = (-1/2 : ℂ) - I * t := by ring
    rw [this]
    rw [complex_im_sub_I_mul]
    simp

  have h3 : ‖(-1/2 - I * t : ℂ)‖ ≥ |(-1/2 - I * t : ℂ).im| := Complex.abs_im_le_norm _

  rw [h2] at h3
  rw [abs_neg] at h3

  have h4 : ‖(-1/2 - I * t : ℂ)‖ > 1 := lt_of_lt_of_le ht h3

  linarith [h4, hs]

lemma D1cinTt (t : ℝ) (ht : |t| > 1) :
    closedBall (3/2 + I * t : ℂ) 1 ⊆ {s : ℂ | s ≠ 1} := by
                                           
  exact fun s hs => D1cinTt_pre t ht s hs

lemma Complex_I_mul_ofReal_re (r : ℝ) : (I * (r : ℂ)).re = 0 := by
  have h : (I * (r : ℂ)).re = -(r : ℂ).im := Complex.I_mul_re (r : ℂ)
  rw [h]
  simp

lemma fc_analytic_normalized (c : ℂ) (f : ℂ → ℂ)
    (h_analytic : AnalyticOnNhd ℂ f (closedBall c 1)) (h_nonzero : f c ≠ 0) :
    (AnalyticOnNhd ℂ (fun z => f (z + c) / f c) (closedBall (0 : ℂ) 1)) ∧ (fun z => f (z + c) / f c) 0 = 1 := by
  constructor
  ·                                  
    apply AnalyticOnNhd.div
    ·                                                  
      apply AnalyticOnNhd.comp h_analytic
      ·                          
        intro z _
        exact analyticAt_id.add analyticAt_const
      ·                                                    
        intro z hz
        rw [mem_closedBall] at hz ⊢
        rw [Complex.dist_eq] at hz ⊢
                                                   
        convert (preTransparency := .instances) hz using 1
        all_goals try with_reducible_and_instances rfl
        ring_nf
    ·                                          
      exact analyticOnNhd_const
    ·                           
      intro z _
      exact h_nonzero
  ·                                              
    simpa using h_nonzero

lemma fc_bound (B : ℝ) (_hB : B > 1) (R : ℝ) (_hRpos : 0 < R) (_hR : R < 1) (c : ℂ) (f : ℂ → ℂ) (_h_nonzero : f c ≠ 0)
    (h_bound : ∀ z ∈ closedBall c R, ‖f z‖ ≤ B) :
    ∀ z ∈ closedBall (0 : ℂ) R, ‖(fun w => f (w + c) / f c) z‖ ≤ B / ‖f c‖ := by
  intro z hz
  have hz' : ‖z‖ ≤ R := by
    simpa [mem_closedBall, Complex.dist_eq] using hz
  have hz_plus : z + c ∈ closedBall c R := by
    have : ‖(z + c) - c‖ ≤ R := by simpa [add_sub_cancel] using hz'
    simpa [mem_closedBall, Complex.dist_eq] using this
  have hfb : ‖f (z + c)‖ ≤ B := h_bound (z + c) hz_plus
  have hnorm : ‖f (z + c) / f c‖ = ‖f (z + c)‖ / ‖f c‖ := by
    simp [div_eq_mul_inv, norm_inv]
  have : ‖f (z + c)‖ / ‖f c‖ ≤ B / ‖f c‖ :=
    div_le_div_of_nonneg_right hfb (norm_nonneg _)
  simpa [hnorm] using this

lemma fc_zeros (r : ℝ) (_h : r > 0) (c : ℂ) (f : ℂ → ℂ) (h_nonzero : f c ≠ 0)
  (_h_analytic : AnalyticOnNhd ℂ f (closedBall c 1)) :
    (zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)) = (fun ρ => ρ - c) '' (zerosetKfRc r c f) := by
  ext ρ'; constructor
  · intro hmem
    rcases hmem with ⟨hball, hzero⟩
                                                                     
    have hprod : f (ρ' + c) * (f c)⁻¹ = 0 := by simpa [div_eq_mul_inv] using hzero
    have hnum0 : f (ρ' + c) = 0 := by
      rcases mul_eq_zero.mp hprod with hnum | hinv
      · exact hnum
      · have : (f c)⁻¹ ≠ 0 := inv_ne_zero h_nonzero
        exact (this hinv).elim
    refine ⟨ρ' + c, ?_, ?_⟩
    ·                                   
      have hdist0 : dist ρ' (0 : ℂ) ≤ r := by simpa [mem_closedBall] using hball
      have hdist1 : dist (ρ' + c) c ≤ r := by
        simpa [Complex.dist_eq, add_sub_cancel] using hdist0
      have hmem_ball : ρ' + c ∈ closedBall c r := by
        simpa [mem_closedBall] using hdist1
      exact And.intro hmem_ball hnum0
    ·                     
      simp
  · intro him
    rcases him with ⟨y, hy_mem, hy_eq⟩
                                           
    subst hy_eq
    rcases hy_mem with ⟨hy_ball, hy_zero⟩
    refine And.intro ?_ ?_
    ·                            
      have hdist : dist y c ≤ r := by simpa [mem_closedBall] using hy_ball
      have hdist0 : dist (y - c) (0 : ℂ) ≤ r := by
        simpa [Complex.dist_eq, sub_zero] using hdist
      simpa [mem_closedBall] using hdist0
    ·                             
      simp [sub_add_cancel, hy_zero]

lemma DminusK (r1 : ℝ) (R1 : ℝ) (_hr1 : r1 > 0) (_hR1 : R1 > 0) (c : ℂ) (f : ℂ → ℂ)
    (_h_analytic : AnalyticOnNhd ℂ f (closedBall c 1)) (h_nonzero : f c ≠ 0) :
    ∀ z : ℂ, z ∈ closedBall (0 : ℂ) r1 \ zerosetKfRc R1 (0 : ℂ) (fun w => f (w + c) / f c) ↔
             z + c ∈ closedBall c r1 \ zerosetKfRc R1 c f := by
  intro z
  constructor
  ·                                                                             
    intro ⟨hz_ball, hz_not_zero⟩
    constructor
    ·                                
      have hdist : dist z (0 : ℂ) ≤ r1 := by simpa [mem_closedBall] using hz_ball
      have hdist_c : dist (z + c) c ≤ r1 := by
        simpa [Complex.dist_eq, add_sub_cancel] using hdist
      simpa [mem_closedBall] using hdist_c
    ·                                   
      intro h_contra
      apply hz_not_zero
                                                                                              
      rcases h_contra with ⟨hz_c_ball, hz_c_zero⟩
      constructor
      ·                            
        have hdist_c : dist (z + c) c ≤ R1 := by simpa [mem_closedBall] using hz_c_ball
        have hdist_0 : dist z (0 : ℂ) ≤ R1 := by
          simpa [Complex.dist_eq, add_sub_cancel] using hdist_c
        simpa [mem_closedBall] using hdist_0
      ·                            
        have : f (z + c) = 0 := hz_c_zero
        simp [this, zero_div]
  ·                                                                             
    intro ⟨hz_c_ball, hz_c_not_zero⟩
    constructor
    ·                            
      have hdist_c : dist (z + c) c ≤ r1 := by simpa [mem_closedBall] using hz_c_ball
      have hdist_0 : dist z (0 : ℂ) ≤ r1 := by
        simpa [Complex.dist_eq, add_sub_cancel] using hdist_c
      simpa [mem_closedBall] using hdist_0
    ·                                                        
      intro h_contra
      apply hz_c_not_zero
                                                                                              
      rcases h_contra with ⟨hz_ball, hz_zero⟩
      constructor
      ·                                
        have hdist_0 : dist z (0 : ℂ) ≤ R1 := by simpa [mem_closedBall] using hz_ball
        have hdist_c : dist (z + c) c ≤ R1 := by
          simpa [Complex.dist_eq, add_sub_cancel] using hdist_0
        simpa [mem_closedBall] using hdist_c
      ·                      
        have h_div_zero : f (z + c) / f c = 0 := hz_zero
        have h_mul_zero : f (z + c) * (f c)⁻¹ = 0 := by simpa [div_eq_mul_inv] using h_div_zero
        cases' mul_eq_zero.mp h_mul_zero with h_num h_inv
        · exact h_num
        · have : (f c)⁻¹ ≠ 0 := inv_ne_zero h_nonzero
          exact (this h_inv).elim

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.Erdos970_Sobolev
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970

open _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance instCoeFunForallReal : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun

end CS

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.Erdos970_Rectangle
attribute [-simp] _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970

open _root_.Complex _root_.Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

def RectangleBorder (z w : ℂ) : Set ℂ :=
  [[z.re, w.re]] ×ℂ {z.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪
    [[z.re, w.re]] ×ℂ {w.im} ∪ {w.re} ×ℂ [[z.im, w.im]]

@[simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl

@[simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm :=
  rfl

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.Erdos970_ResidueCalcOnRectangles
attribute [-simp] _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970

open _root_.Complex BigOperators _root_.Nat Classical _root_.Real Topology _root_.Filter
open _root_.Set _root_.MeasureTheory _root_.intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

noncomputable def HIntegral (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
    ∫ x in x₁..x₂, f (x + y * _root_.Complex.I)

noncomputable def VIntegral (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
    _root_.Complex.I • ∫ y in y₁..y₂, f (x + y * _root_.Complex.I)

noncomputable def RectangleIntegral (f : ℂ → E) (z w : ℂ) : E :=
    HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im +
    VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im

noncomputable abbrev RectangleIntegral' (f : ℂ → E) (z w : ℂ) : E :=
    (1 / (2 * π * _root_.Complex.I)) • RectangleIntegral f z w

noncomputable def VerticalIntegral (f : ℂ → E) (σ : ℝ) : E :=
    _root_.Complex.I • ∫ t : ℝ, f (σ + t * _root_.Complex.I)

noncomputable abbrev VerticalIntegral' (f : ℂ → E) (σ : ℝ) : E :=
    (1 / (2 * π * _root_.Complex.I)) • VerticalIntegral f σ

abbrev HolomorphicOn (f : ℂ → E) (s : Set ℂ) : Prop :=
    DifferentiableOn ℂ f s

theorem existsDifferentiableOn_of_bddAbove [CompleteSpace E]
    {s : Set ℂ} {c : ℂ} (hc : s ∈ nhds c)
    (hd : HolomorphicOn f (s \ {c}))
    (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    ∃ (g : ℂ → E),
      HolomorphicOn g s ∧ Set.EqOn f g (s \ {c}) :=
  ⟨Function.update f c (limUnder (𝓝[{c}ᶜ] c) f),
    differentiableOn_update_limUnder_of_bddAbove hc hd hb,
    fun z hz ↦ if h : z = c then (hz.2 h).elim
      else by simp [h]⟩

def RectangleBorderIntegrable (f : ℂ → E) (z w : ℂ) : Prop :=
    IntervalIntegrable (fun x => f (x + z.im * _root_.Complex.I)) volume z.re w.re ∧
    IntervalIntegrable (fun x => f (x + w.im * _root_.Complex.I)) volume z.re w.re ∧
    IntervalIntegrable (fun y => f (w.re + y * _root_.Complex.I)) volume z.im w.im ∧
    IntervalIntegrable (fun y => f (z.re + y * _root_.Complex.I)) volume z.im w.im

lemma IsBigO_to_BddAbove {f : ℂ → ℂ} {p : ℂ}
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    ∃ U ∈ 𝓝 p, BddAbove (norm ∘ f '' (U \ {p})) := by
  simp only [isBigO_iff, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one] at f_near_p
  obtain ⟨c, hc⟩ := f_near_p
  dsimp [Filter.Eventually, nhdsWithin] at hc
  rw [mem_inf_principal'] at hc
  obtain ⟨U, hU, ⟨U_is_open, p_in_U⟩⟩ := mem_nhds_iff.mp hc
  use U
  constructor
  · exact IsOpen.mem_nhds U_is_open p_in_U
  · refine bddAbove_def.mpr ?_
    use c
    intro y hy
    simp only [Function.comp_apply, mem_image, Set.mem_sdiff, mem_singleton_iff] at hy
    obtain ⟨x, ⟨x_in_U, x_not_p⟩, fxy⟩ := hy
    rw [← fxy]
    simpa [x_not_p] using hU x_in_U

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.Erdos970_ZetaBounds
attribute [-simp] _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970


open _root_.Complex Topology _root_.Filter Interval _root_.Set Asymptotics

local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

theorem ResidueOfTendsTo {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (hU : U ∈ 𝓝 p)
    (hf : HolomorphicOn f (U \ {p}))
    {A : ℂ}
    (h_limit : Tendsto (fun s ↦ (s - p) * f s) (𝓝[≠] p) (𝓝 A)) :
    ∃ V ∈ 𝓝 p,
    BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (V \ {p})) := by
                                                                
  have h_event : ∀ᶠ s in 𝓝[≠] p, ‖(s - p) * f s - A‖ < 1 := by
    simp_rw [← dist_eq_norm_sub]
    exact h_limit.eventually (Metric.ball_mem_nhds _ (by norm_num))
  have h_event_nhds :
      ∀ᶠ s in 𝓝 p, s ≠ p → ‖(s - p) * f s - A‖ < 1 := by
    exact (eventually_nhdsWithin_iff).1 h_event
  rcases (eventually_nhds_iff.1 h_event_nhds) with ⟨V₀, hV₀_mem, hV₀_prop⟩
  have h_bound :
      ∀ s, s ∈ V₀ \ {p} → ‖(s - p) * f s‖ ≤ ‖A‖ + 1 := by
    intro s hs
    rcases hs with ⟨hV₀, hsne⟩
    calc ‖(s - p) * f s‖ = ‖((s - p) * f s - A) + A‖ := by
          ring_nf
        _ ≤ ‖(s - p) * f s - A‖ + ‖A‖ := norm_add_le ((s - p) * f s - A) A
        _ ≤ 1 + ‖A‖ := add_le_add_left (le_of_lt (hV₀_mem s hV₀ hsne)) ‖A‖
        _ = ‖A‖ + 1 := add_comm 1 ‖A‖
  have h_bdd :
      BddAbove (norm ∘ (fun s ↦ (s - p) * f s) '' (V₀ \ {p})) := by
    refine ⟨‖A‖ + 1, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact h_bound s hs
                                                                 
  set W : Set ℂ := V₀ ∩ U with hW_def
  have hW_mem : (W : Set ℂ) ∈ 𝓝 p := inter_mem (IsOpen.mem_nhds hV₀_prop.1 hV₀_prop.2) hU
  have h_subset_V₀ : (W \ {p}) ⊆ (V₀ \ {p}) := by
    intro z hz; exact ⟨hz.1.1, hz.2⟩
  have h_prod_holo : HolomorphicOn (fun z ↦ (z - p) * f z) (W \ {p}) := by
    have h_id : HolomorphicOn (fun z : ℂ ↦ z - p) (W \ {p}) :=
      Differentiable.differentiableOn (Differentiable.sub_const differentiable_fun_id p)
    have hfW : HolomorphicOn f (W \ {p}) := by
      apply hf.mono
      exact Set.sdiff_subset_sdiff_left inter_subset_right
    simpa using! h_id.mul hfW
  have h_bdd_W : BddAbove (norm ∘ (fun s ↦ (s - p) * f s) '' (W \ {p})) :=
    h_bdd.mono (image_mono h_subset_V₀)
                                                                    
  obtain ⟨g, hg_holo, hg_eq⟩ :=
    existsDifferentiableOn_of_bddAbove hW_mem h_prod_holo h_bdd_W
  have h_event_eq :
      (fun z ↦ g z) =ᶠ[𝓝[≠] p] fun z ↦ (z - p) * f z := by
    have hW_diff_mem : (W \ {p} : Set ℂ) ∈ 𝓝[≠] p :=
      sdiff_mem_nhdsWithin_compl hW_mem {p}
    exact (hg_eq.eventuallyEq_of_mem hW_diff_mem).symm
  have h_tendsto_gA : Tendsto g (𝓝[≠] p) (𝓝 A) :=
      h_limit.congr' (id (EventuallyEq.symm h_event_eq))
  have hpW : p ∈ W := by
    exact mem_of_mem_nhds hW_mem
  have h_cont_g : ContinuousAt g p := by
    apply (hg_holo.continuousOn.continuousWithinAt hpW).continuousAt hW_mem
  have h_tendsto_gp : Tendsto g (𝓝[≠] p) (𝓝 (g p)) :=
    h_cont_g.tendsto.mono_left inf_le_left
  have g_p_eq : g p = A :=
    tendsto_nhds_unique' (NormedField.nhdsNE_neBot p) h_tendsto_gp h_tendsto_gA
  let q : ℂ → ℂ := fun z ↦ (g z - A) / (z - p)
  have h_deriv : HasDerivAt g (deriv g p) p := by
    exact DifferentiableOn.hasDerivAt hg_holo hW_mem
  have h_q_limit : Tendsto q (𝓝[≠] p) (𝓝 (deriv g p)) := by
    rw [hasDerivAt_iff_tendsto_slope] at h_deriv
    unfold slope at h_deriv
    simp only [vsub_eq_sub, smul_eq_mul, inv_mul_eq_div, g_p_eq] at h_deriv
    exact h_deriv
  have h_event_q : ∀ᶠ z in 𝓝[≠] p, ‖q z - deriv g p‖ < 1 := by
    simp_rw [← dist_eq_norm_sub]
    exact h_q_limit.eventually (Metric.ball_mem_nhds _ (by norm_num))
  have h_event_q_nhds : ∀ᶠ z in 𝓝 p, z ≠ p → ‖q z - deriv g p‖ < 1 := by
    simpa using (eventually_nhdsWithin_iff).1 h_event_q
  rcases (eventually_nhds_iff.1 h_event_q_nhds) with
    ⟨V₁, hV₁_mem, hV₁_prop⟩
  have h_q_bound :
      ∀ z, z ∈ V₁ \ {p} → ‖q z‖ ≤ ‖deriv g p‖ + 1 := by
    intro z hz
    rcases hz with ⟨hV₁, hz_ne⟩
    calc ‖q z‖ = ‖(q z - deriv g p) + (deriv g p)‖ := by
          ring_nf
        _ ≤ ‖q z - deriv g p‖ + ‖deriv g p‖ := norm_add_le (q z - deriv g p) (deriv g p)
        _ ≤ 1 + ‖deriv g p‖  := add_le_add_left (le_of_lt (hV₁_mem z hV₁ hz_ne)) ‖deriv g p‖
        _ = ‖deriv g p‖ + 1 := add_comm 1 ‖deriv g p‖
                                                   
  have h_eq_diff :
      EqOn (fun z ↦ f z - A * (z - p)⁻¹) q (W \ {p}) := by
    intro z hz
    simp only
    have hz_ne : (z - p) ≠ 0 := sub_ne_zero.mpr hz.2
    have hgz : g z = (z - p) * f z := by
      exact id (EqOn.symm hg_eq) hz
    simp only [hgz, q]
    field_simp
  apply IsBigO_to_BddAbove
  rw [isBigO_iff]
  use ‖deriv g p‖ + 1
  apply eventually_nhdsWithin_iff.mpr
  filter_upwards [IsOpen.mem_nhds hV₁_prop.1 hV₁_prop.2, hW_mem] with z hV₁ hW z_ne_p
  specialize h_eq_diff ⟨ hW, z_ne_p⟩
  simp only [Pi.sub_apply, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary,
    mul_one] at h_eq_diff ⊢
  rw [h_eq_diff]
  exact h_q_bound _ ⟨hV₁, z_ne_p⟩

theorem riemannZetaResidue :
    ∃ U ∈ 𝓝 1, BddAbove (norm ∘ (ζ - (fun s ↦ (s - 1)⁻¹)) '' (U \ {1})) := by
  have zeta_holc : HolomorphicOn ζ (univ \ {1}) := by
    intro y hy
    exact DifferentiableAt.differentiableWithinAt <| differentiableAt_riemannZeta hy.2
  convert (preTransparency := .instances) ResidueOfTendsTo univ_mem zeta_holc riemannZeta_residue_one using 6
  all_goals try with_reducible_and_instances rfl
  simp

theorem deriv_eqOn_of_eqOn_punctured (f g : ℂ → ℂ) (U : Set ℂ) (p : ℂ)
    (hU_open : IsOpen U)
    (h_eq : EqOn f g (U \ {p})) :
    EqOn (deriv f) (deriv g) (U \ {p}) := by
  intro x hx
  apply EventuallyEq.deriv_eq
  filter_upwards [IsOpen.mem_nhds (hU_open.sdiff isClosed_singleton) hx] with t ht using h_eq ht

theorem analytic_deriv_bounded_near_point
    (f : ℂ → ℂ) {U : Set ℂ} {p : ℂ} (hU : IsOpen U) (hp : p ∈ U) (hf : HolomorphicOn f U) :
    (deriv f) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have U_in_filter : U ∈ 𝓝 p := by
    exact IsOpen.mem_nhds hU hp
  have T := (analyticOn_iff_differentiableOn hU).mpr hf
  have T2 : ContDiffOn ℂ 1 f U :=
      DifferentiableOn.contDiffOn hf hU
  have T3 : ContinuousOn (fun x ↦ ((deriv f) x)) U := by
    apply T2.continuousOn_deriv_of_isOpen hU (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have T4 := T3.continuousAt U_in_filter
  have T5 : (deriv f) =O[𝓝 p] (1 : ℂ → ℂ) :=
    T4.norm.isBoundedUnder_le.isBigO_one ℂ
  exact Asymptotics.IsBigO.mono T5 inf_le_left

theorem derivative_const_plus_product {g : ℂ → ℂ} (A p x : ℂ) (hg : DifferentiableAt ℂ g x) :
    deriv ((fun _ ↦ A) + g * fun s ↦ s - p) x = deriv g x * (x - p) + g x := by
  rw [deriv_add (by fun_prop) (by fun_prop), deriv_const, deriv_mul hg (by fun_prop)]
  simp

lemma deriv_inv_sub {x p : ℂ} (hp : x ≠ p) :
  deriv (fun z => (z - p)⁻¹) x =  -((x - p) ^ 2)⁻¹ := by
  rw [deriv_fun_inv'' (by fun_prop) (by grind)]
  simp
  field

theorem deriv_f_minus_A_inv_sub_clean (f : ℂ → ℂ) (A x p : ℂ)
    (hf : DifferentiableAt ℂ f x) (hp : x ≠ p) :
    deriv (f  - (fun z ↦ A * (z - p)⁻¹)) x = deriv f x + A * ((x - p) ^ 2)⁻¹ := by
  have h1 : DifferentiableAt ℂ (fun z => (z - p)⁻¹) x := by
    fun_prop (disch := grind)
  rw [deriv_sub hf (h1.const_mul A), deriv_const_mul A h1, deriv_inv_sub hp]
  ring

theorem nonZeroOfBddAbove {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    ∃ V ∈ 𝓝 p, IsOpen V ∧ ∀ s ∈ V \ {p}, f s ≠ 0 := by

  have h_decomp : ∀ s, f s = (f s - A * (s - p)⁻¹) + A * (s - p)⁻¹ := by
    intro s
    ring
                                      
  obtain ⟨M, hM⟩ := f_near_p

  have A_norm_pos : 0 < ‖A‖ := norm_pos_iff.mpr A_ne_zero
                                                                        
  let δ := ‖A‖ / (‖M‖ + 1)
  have δ_pos : 0 < δ := by
    refine div_pos A_norm_pos (add_pos_of_nonneg_of_pos (norm_nonneg M) one_pos)
                                                                            
  obtain ⟨V, hV_open, hV_mem, hV_sub⟩ : ∃ V, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∩ Metric.ball p δ := by
                                     
    obtain ⟨W, hW_sub, hW_open, hW_mem⟩ := mem_nhds_iff.mp U_in_nhds
    let V := W ∩ Metric.ball p δ
    have VNp : V ∈ 𝓝 p := (𝓝 p).inter_mem (IsOpen.mem_nhds hW_open hW_mem)
      (Metric.ball_mem_nhds p δ_pos)
    exact ⟨V, IsOpen.inter hW_open Metric.isOpen_ball, mem_of_mem_nhds VNp,
      inter_subset_inter_left _ hW_sub⟩
  use V, mem_nhds_iff.mpr ⟨V, subset_refl V, hV_open, hV_mem⟩, hV_open
                    
  intro s hs
  have hs_in_U : s ∈ U := hV_sub hs.1 |>.1
  have hs_near_p : dist s p < δ := hV_sub hs.1 |>.2
  have hs_ne_p : s ≠ p := hs.2
                                                              
  rw [h_decomp s]
                                 
  have bound_first : ‖f s - A * (s - p)⁻¹‖ ≤ M := by
    apply hM
    exact ⟨s, ⟨hs_in_U, hs_ne_p⟩, rfl⟩
                                      
  have large_second : ‖M‖ + 1 < ‖A * (s - p)⁻¹‖ := by
    rw [norm_mul, norm_inv, ← div_eq_mul_inv]
    rw [lt_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs_ne_p))]
    rw [mul_comm, ← lt_div_iff₀ (add_pos_of_nonneg_of_pos (norm_nonneg M) one_pos)]
    rw [dist_eq_norm_sub] at hs_near_p
    exact hs_near_p
                                                
  by_contra h_zero
                                                                  
  rw [add_eq_zero_iff_eq_neg] at h_zero
  rw [h_zero, norm_neg] at bound_first
                                    
  have : ‖M‖ + 1 < ‖M‖ := (lt_of_lt_of_le (lt_of_lt_of_le large_second bound_first)
    (Real.le_norm_self M))
  norm_num at this

theorem logDerivResidue' {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (U_is_open : IsOpen U)
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by

  have simpleHolo : HolomorphicOn (fun s ↦ A / (s - p)) (U \ {p}) := by
    apply DifferentiableOn.mono (t := {p}ᶜ)
    · apply DifferentiableOn.div
      · exact differentiableOn_const _
      · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
      · exact fun x hx => by rw [sub_ne_zero]; exact hx
    · rintro s ⟨_, hs⟩ ; exact hs

  have f_minus_pole_is_holomorphic : HolomorphicOn (f - (fun s ↦ A * (s - p)⁻¹)) (U \ {p}) := by
    exact (DifferentiableOn.sub_iff_right holc).mpr simpleHolo

  let ⟨g, ⟨g_is_holomorphic, g_is_f_minus_pole⟩⟩ := existsDifferentiableOn_of_bddAbove
    U_in_nhds f_minus_pole_is_holomorphic f_near_p

  let h := (fun _ ↦ A) + g * (fun (s : ℂ) ↦ (s - p))

  have linear_is_holomorphic : HolomorphicOn (fun (s : ℂ ) ↦ (s - p)) U := by
    exact DifferentiableOn.sub_const differentiableOn_id p

  have h_is_holomorphic : HolomorphicOn h U := by
    have T := DifferentiableOn.mul g_is_holomorphic linear_is_holomorphic
    exact DifferentiableOn.const_add A T

  have h_continuous : ContinuousOn h U :=
    by exact DifferentiableOn.continuousOn h_is_holomorphic

  have deriv_h_identity : ∀x ∈ (U \ {p}), (deriv h) x = f x + (deriv f x) * (x - p) := by
    intro x x_in_u_not_p
    have x_in_u : x ∈ U := by exact Set.mem_of_mem_sdiff x_in_u_not_p
    have x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp x_in_u_not_p).2

    have weird : U ∈ 𝓝 x := by
      exact IsOpen.mem_nhds (U_is_open) (x_in_u)

    rw [derivative_const_plus_product, ← g_is_f_minus_pole x_in_u_not_p,
      ← deriv_eqOn_of_eqOn_punctured _ _ U p U_is_open g_is_f_minus_pole x_in_u_not_p,
      deriv_f_minus_A_inv_sub_clean]
    · simp only [Pi.sub_apply]
      have := sub_ne_zero_of_ne x_not_p
      field_simp
      ring
    · apply holc.differentiableAt
      exact Filter.inter_mem weird <| compl_singleton_mem_nhds x_not_p
    · exact x_not_p
    · exact g_is_holomorphic.differentiableAt weird
  have h_identity : ∀x ∈ (U \ {p}), h x = (f x) * (x - p)  := by
    intro x x_in_u_not_p
    have hyp_x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp x_in_u_not_p).2
    simp only [h, Pi.add_apply, Pi.mul_apply]
    rw [← g_is_f_minus_pole x_in_u_not_p]
    simp only [Pi.sub_apply]
    field [sub_ne_zero.mpr hyp_x_not_p]
  have log_deriv_f_plus_pole_equal_log_deriv_h :
      EqOn (deriv f * f⁻¹ + fun s ↦ (s - p)⁻¹) ((deriv h) * h⁻¹) (U \ {p}) := by
    simp only [Set.mem_sdiff, mem_singleton_iff, ne_eq, and_imp, Function.comp_apply, Pi.sub_apply,
      DifferentiableOn.sub_iff_right, differentiableOn_const, DifferentiableOn.fun_sub_iff_left,
      holc] at *
    intro x hyp_x
    have x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp hyp_x).2
    have x_in_u : x ∈ U := by exact Set.mem_of_mem_sdiff hyp_x
    simp only [Pi.add_apply, Pi.mul_apply, Pi.inv_apply]
    rw [deriv_h_identity _ x_in_u x_not_p, h_identity _ x_in_u x_not_p]

    field [sub_ne_zero.mpr x_not_p, non_zero x (x_in_u) x_not_p]
  have h_inv_bounded :
      h⁻¹ =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    have : ContinuousAt h⁻¹ p := by
      apply ContinuousOn.continuousAt h_continuous U_in_nhds |>.inv₀
      simp [h, A_ne_zero]
    exact Asymptotics.IsBigO.mono (this.norm.isBoundedUnder_le.isBigO_one ℂ) inf_le_left

  have h_deriv_bounded :
        (deriv h) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
          analytic_deriv_bounded_near_point h U_is_open
            (by exact mem_of_mem_nhds U_in_nhds) h_is_holomorphic

  have h_log_deriv_bounded :
    ((deriv h) * h⁻¹) =O[𝓝[≠] p] (1 : ℂ → ℂ)  := by
      have T := Asymptotics.IsBigO.mul h_deriv_bounded h_inv_bounded
      exact IsBigO.of_const_mul_right T

  have u_not_p_in_filter : U \ {p} ∈ 𝓝[≠] p := by
    exact sdiff_mem_nhdsWithin_compl U_in_nhds {p}
  have T := Set.EqOn.eventuallyEq_of_mem log_deriv_f_plus_pole_equal_log_deriv_h u_not_p_in_filter
  exact EventuallyEq.trans_isBigO T h_log_deriv_bounded

theorem logDerivResidue {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    by
      let ⟨U', ⟨a,b,c⟩⟩ := mem_nhds_iff.mp U_in_nhds
      have W : (U' \ {p}) ⊆ U' := by
        exact Set.sdiff_subset

      have T : (U' \ {p}) ⊆ (U \ {p}) := by
        exact Set.sdiff_subset_sdiff a (subset_refl _)

      refine logDerivResidue' b ?_ ?_ (IsOpen.mem_nhds b c) A_ne_zero ?_
      · intro x hyp_x
        exact non_zero x <| T hyp_x
      · exact DifferentiableOn.mono holc T
      · exact (f_near_p.mono (image_mono (Set.sdiff_subset_sdiff a (subset_refl _))))

lemma BddAbove_to_IsBigO {f : ℂ → ℂ} {p : ℂ}
    {U : Set ℂ} (hU : U ∈ 𝓝 p) (bdd : BddAbove (norm ∘ f '' (U \ {p}))) :
    f =O[𝓝[≠] p] (1 : ℂ → ℂ)  := by
  dsimp [BddAbove, upperBounds] at bdd
  rcases bdd with ⟨C, hC⟩

  have h : ∀ x ∈ U \ {p}, ‖f x‖ ≤ C := by
    intro x hx
    have fx_is_norm : ‖f x‖ ∈ norm ∘ f ''(U \ {p}) := by
      exact ⟨x, hx, rfl⟩
    exact hC fx_is_norm

  rw [Asymptotics.isBigO_iff]
  use C
  rw [eventually_nhdsWithin_iff]
  simp only [Set.mem_sdiff, mem_singleton_iff, and_imp, mem_compl_iff, Pi.one_apply, one_mem,
    CStarRing.norm_of_mem_unitary, mul_one] at h ⊢
  filter_upwards [hU] using h

theorem logDerivResidue'' {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    ∃ V ∈ 𝓝 p, BddAbove (norm ∘ (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) '' (V \ {p})) := by
  apply IsBigO_to_BddAbove
  exact logDerivResidue non_zero holc U_in_nhds A_ne_zero f_near_p

theorem riemannZetaLogDerivResidue :
    ∃ U ∈ 𝓝 1, BddAbove (norm ∘ (-(ζ' / ζ) - (fun s ↦ (s - 1)⁻¹)) '' (U \ {1})) := by
  obtain ⟨U,U_in_nhds, hU⟩ := riemannZetaResidue
  have hU' : BddAbove (norm ∘ (ζ - fun s ↦ 1 * (s - 1)⁻¹) '' (U \ {1})) := by
    simp only [Function.comp_apply, Pi.sub_apply, one_mul] at hU ⊢
    exact hU
  obtain ⟨V,V_in_nhds, V_is_open, hV⟩ := nonZeroOfBddAbove U_in_nhds one_ne_zero hU'
  let W := V ∩ interior U
  have hW : ∀ s ∈ W \ {1}, ζ s ≠ 0 := by
    intro s hs
    have s_in_V_diff : s ∈ V \ {1} := ⟨hs.1.1, hs.2⟩
    exact hV s s_in_V_diff
  have ζ_holc: HolomorphicOn ζ (W \ {1}) := by
    intro y hy
    simp only [Set.mem_sdiff, mem_singleton_iff] at hy
    refine DifferentiableAt.differentiableWithinAt ?_
    apply differentiableAt_riemannZeta hy.2
  have W_in_nhds : W ∈ 𝓝 1 := by
    refine inter_mem V_in_nhds ?_
    exact interior_mem_nhds.mpr U_in_nhds
  have := logDerivResidue'' hW ζ_holc W_in_nhds one_ne_zero
  have HW : BddAbove (norm ∘ (ζ - fun s ↦ (s - 1)⁻¹) '' (W \ {1})) := by
    obtain ⟨c, hc⟩ := bddAbove_def.mp hU
    apply bddAbove_def.mpr
    use c
    rintro y ⟨x, x_in_W, fxy⟩
    apply hc
    exact ⟨x, ⟨interior_subset x_in_W.1.2, x_in_W.2⟩, fxy⟩
  simp only [one_mul] at this
  have aux: ∀ a, ‖-(deriv ζ a / ζ a) - (a - 1)⁻¹‖ = ‖(deriv ζ a / ζ a) + (a - 1)⁻¹‖ := by
    intro a
    calc ‖-(deriv ζ a / ζ a) - (a - 1)⁻¹‖
         = ‖-((deriv ζ a / ζ a) + (a - 1)⁻¹)‖ := by ring_nf
       _ = ‖(deriv ζ a / ζ a) + (a - 1)⁻¹‖ := by rw [norm_neg]
  simp only [Function.comp_apply, Pi.sub_apply] at hU
  simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply, aux]
  apply this HW

theorem riemannZetaLogDerivResidueBigO :
    (-ζ' / ζ - fun z ↦ (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
  obtain ⟨U, hU, bdd⟩ := riemannZetaLogDerivResidue
  convert (preTransparency := .instances) BddAbove_to_IsBigO hU bdd using 2
  all_goals try with_reducible_and_instances rfl
  rw [neg_div]

open _root_.ArithmeticFunction (vonMangoldt)

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.Erdos970_Z0
attribute [-simp] _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970

open _root_.Complex Topology _root_.Filter Interval _root_.Set Asymptotics

local notation (name := riemannzeta1) "ζ" => riemannZeta
local notation (name := derivriemannzeta1) "ζ'" => deriv riemannZeta

lemma Z0bound_aux :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0)) (fun (delta : ℝ) => -(ζ' / ζ) ((1 : ℂ) + delta) - (1 / (delta : ℂ))) (fun _ => (1 : ℂ)) := by

  let F := fun s : ℂ => -(ζ' / ζ) s - (s - 1)⁻¹

  have h_F_bigO : F =O[𝓝[≠] 1] (1 : ℂ → ℂ) := by
    have h_fun_eq : F = (-ζ' / ζ - fun z ↦ (z - 1)⁻¹) := by
      ext s
      simp only [F, Pi.sub_apply, Pi.neg_apply, Pi.div_apply, neg_div]
    rw [h_fun_eq]
    exact riemannZetaLogDerivResidueBigO

  let u := fun (delta : ℝ) => (1 : ℂ) + delta
  have h_tendsto : Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (𝓝[≠] 1) := by

    apply tendsto_inf.mpr
    constructor
    ·                                     
      have h_cont : Continuous u := continuous_const.add continuous_ofReal
                                                             
      have h_tendsto_nhds : Tendsto u (𝓝 0) (𝓝 (u 0)) := h_cont.continuousAt.tendsto
                                                                     
      simp only [u, Complex.ofReal_zero, add_zero] at h_tendsto_nhds

      exact h_tendsto_nhds.mono_left nhdsWithin_le_nhds
    ·                                                  
                                                      
      simp
                                                  
      filter_upwards [self_mem_nhdsWithin] with delta h_delta_pos
      simp only [u]

      refine add_ne_left.mpr ?_
      rw [Complex.ofReal_ne_zero]
      exact ne_of_gt h_delta_pos

  have h_comp := h_F_bigO.comp_tendsto h_tendsto

  convert (preTransparency := .instances) h_comp using 1
  all_goals try with_reducible_and_instances rfl
  ext delta
                                                           
  simp only [F, u, Function.comp_apply, Pi.div_apply]
  rw [inv_eq_one_div]
  aesop
  all_goals rfl

lemma Z0bound :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0)) (fun (delta : ℝ) => -logDerivZeta ((1 : ℂ) + delta) - (1 / (delta : ℂ))) (fun _ => (1 : ℂ)) := Z0bound_aux

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.Erdos970_PNT4_ZeroFreeRegion
attribute [-simp] _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970


def zeroZ : Set ℂ := {s : ℂ | riemannZeta s = 0}

def ZetaZerosNearPoint (t : ℝ) : Set ℂ := { ρ : ℂ | ρ ∈ zeroZ ∧ ‖ρ - ((3/2 : ℂ) + t * Complex.I)‖ ≤ (5/6 : ℝ) }

lemma ZetaZerosNearPoint_finite (t : ℝ) : Set.Finite (ZetaZerosNearPoint t) := by
                                  
  let c : ℂ := (3/2 : ℂ) + t * Complex.I
  let R : ℝ := (5/6 : ℝ)
  have hRpos : 0 < R := by norm_num

  let H : ℂ → ℂ := Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1
  have hH_diff : Differentiable ℂ H := by
                                                               
    intro s
    rcases eq_or_ne s 1 with rfl | hs
    ·                                                                                                
      refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
      ·                                             
        filter_upwards [self_mem_nhdsWithin] with t ht
                                                                              
        have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - 1) * riemannZeta u) t := by
          have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) t :=
            (differentiableAt_id.sub_const 1)
          have h2 : DifferentiableAt ℂ riemannZeta t :=
            (differentiableAt_riemannZeta ht)
          exact h1.mul h2
        apply DifferentiableAt.congr_of_eventuallyEq hdiff
        filter_upwards [eventually_ne_nhds ht] with u hu using by
          simp [H, Function.update_of_ne hu]
      ·                                                           
        simpa [H, continuousAt_update_same] using riemannZeta_residue_one
    ·                                                        
      have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - 1) * riemannZeta u) s := by
        have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) s :=
          (differentiableAt_id.sub_const 1)
        have h2 : DifferentiableAt ℂ riemannZeta s :=
          (differentiableAt_riemannZeta hs)
        exact h1.mul h2
      apply DifferentiableAt.congr_of_eventuallyEq hdiff
      filter_upwards [eventually_ne_nhds hs] with u hu using by
        simp [H, Function.update_of_ne hu]

  by_cases hPoleIn : ‖1 - c‖ ≤ R
  ·                                                         
    let g : ℂ → ℂ := fun z => H (z + c)
                                                                                                   
    have hzeta_c_ne : riemannZeta c ≠ 0 := by
                                     
      have : c.re = (3/2 : ℝ) := by
        simp [c, Complex.add_re, Complex.mul_re, Complex.I_re]
      have hgt : c.re > 1 := by simpa [this] using (by norm_num : (3:ℝ)/2 > 1)
                                                             
      exact riemannZeta_ne_zero_of_one_le_re (by
                        
        have : (1 : ℝ) < c.re := hgt
        exact le_of_lt this)
    have hg_nonzero : ∃ z ∈ Metric.ball (0 : ℂ) R, g z ≠ 0 := by
                                                           
      have h0in : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
        simpa [Metric.mem_ball, Complex.dist_eq] using hRpos
      refine ⟨0, h0in, ?_⟩
                                                             
      have hcne1 : c ≠ (1 : ℂ) := by
        intro hc; have hcreq : c.re = 1 := by simp [hc, Complex.one_re]
        have : (3 : ℝ) / 2 = (1 : ℝ) := by
          simpa [c, Complex.add_re, Complex.mul_re, Complex.I_re] using hcreq
        norm_num at this
      have hHc : g 0 = H c := by simp [g]
      have : g 0 = (c - 1) * riemannZeta c := by
        simpa [H, Function.update_of_ne hcne1] using hHc
      simpa [this] using mul_ne_zero (sub_ne_zero.mpr (by
                                 
        exact hcne1)) hzeta_c_ne
                                                  
    let Kg : Set ℂ := {ρ : ℂ | ρ ∈ Metric.closedBall (0 : ℂ) R ∧ g ρ = 0}
                                                                        
    have h_subset : ZetaZerosNearPoint t ⊆ {ρ : ℂ | (ρ - c) ∈ Metric.closedBall 0 R ∧ g (ρ - c) = 0} := by
      intro ρ hρ
      rcases hρ with ⟨hzero, hdist⟩
                                          
      have hball : ρ - c ∈ Metric.closedBall 0 R := by
        simpa [Metric.mem_closedBall, Complex.dist_eq, c, sub_eq_add_neg] using hdist
                                                      
      have hρne1 : (ρ : ℂ) ≠ 1 := by
        intro hρ1
                                          
        have hz1_ne : riemannZeta (1 : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
        exact hz1_ne (by simpa [hρ1] using! hzero)
      have hsum : (ρ - c) + c = ρ := by simp [sub_add_cancel]
      have hxne : (ρ - c) + c ≠ (1 : ℂ) := by simpa [hsum] using hρne1
      have hform : g (ρ - c) = (ρ - 1) * riemannZeta ρ := by
        simp [g, H, hsum, Function.update_of_ne hxne]
      have hzeroζ : riemannZeta ρ = 0 := hzero
      have hzero' : g (ρ - c) = 0 := by simp [hform, hzeroζ]
      exact ⟨hball, hzero'⟩
                                                                                                 
    have hg_diff : Differentiable ℂ g := by
      intro z
      have hH := hH_diff (z + c)
      have h_addc : DifferentiableAt ℂ (fun z : ℂ => z + c) z :=
        (differentiableAt_id.add_const c)
      simpa [g] using! hH.comp z h_addc
    have hg_analyticNhd_univ : AnalyticOnNhd ℂ g Set.univ :=
      (Complex.analyticOnNhd_univ_iff_differentiable).2 hg_diff
    have hg_analyticNhd : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) :=
      AnalyticOnNhd.mono hg_analyticNhd_univ (by intro z hz; simp)
    have hNonzero : ∃ z ∈ Metric.ball (0 : ℂ) 1, g z ≠ 0 := by
      rcases hg_nonzero with ⟨z, hz_in, hz_ne⟩
                                        
      have hz_in' : z ∈ Metric.ball (0 : ℂ) 1 := by
        have hRle : (R : ℝ) ≤ 1 := by norm_num
        exact Metric.ball_subset_ball hRle hz_in
      exact ⟨z, hz_in', hz_ne⟩
    have hfiniteKg : Set.Finite Kg :=
      (lem_Contra_finiteKR R hRpos (by norm_num : R < 1) g hg_analyticNhd hNonzero)
                                                                    
    have hTarget_eq : {ρ : ℂ | (ρ - c) ∈ Metric.closedBall 0 R ∧ g (ρ - c) = 0} =
          (fun ρ : ℂ => ρ + c) '' Kg := by
      ext ρ; constructor
      · intro h
        rcases h with ⟨hball, hzero⟩
        refine ⟨ρ - c, ⟨?_, ?_⟩, ?_⟩
        · exact hball
        · exact hzero
        · simp [sub_add_cancel]
      · intro h
        rcases h with ⟨z, ⟨hzball, hz0⟩, rfl⟩
        constructor
        · simpa [sub_add_cancel] using hzball
        · simpa [sub_add_cancel] using hz0
                                                                                    
    have hTarget_fin : Set.Finite {ρ : ℂ | (ρ - c) ∈ Metric.closedBall 0 R ∧ g (ρ - c) = 0} := by
      have himg : Set.Finite ((fun ρ : ℂ => ρ + c) '' Kg) := hfiniteKg.image _
                                                
      exact hTarget_eq ▸ himg
    exact Set.Finite.subset hTarget_fin h_subset
  ·                                             
    let g : ℂ → ℂ := fun z => H (z + c)
                                          
    have hzeta_c_ne : riemannZeta c ≠ 0 := by
      have : c.re = (3/2 : ℝ) := by
        simp [c, Complex.add_re, Complex.mul_re, Complex.I_re]
      have hgt : c.re > 1 := by simpa [this] using (by norm_num : (3:ℝ)/2 > 1)
      exact riemannZeta_ne_zero_of_one_le_re (le_of_lt hgt)
    have hg_nonzero : ∃ z ∈ Metric.ball (0 : ℂ) R, g z ≠ 0 := by
      have h0in : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
        simpa [Metric.mem_ball, Complex.dist_eq] using hRpos
      refine ⟨0, h0in, ?_⟩
      have hcne1 : c ≠ (1 : ℂ) := by
        intro hc; have hcreq : c.re = 1 := by simp [hc, Complex.one_re]
        have : (3 : ℝ) / 2 = (1 : ℝ) := by
          simpa [c, Complex.add_re, Complex.mul_re, Complex.I_re] using hcreq
        norm_num at this
                                      
      have hHc : g 0 = H c := by simp [g]
      have : g 0 = (c - 1) * riemannZeta c := by
        simpa [H, Function.update_of_ne hcne1] using hHc
      simpa [this] using mul_ne_zero (sub_ne_zero.mpr hcne1) hzeta_c_ne
                                          
    let Kg : Set ℂ := {ρ : ℂ | ρ ∈ Metric.closedBall (0 : ℂ) R ∧ g ρ = 0}
                     
    have h_subset : ZetaZerosNearPoint t ⊆ {ρ : ℂ | (ρ - c) ∈ Metric.closedBall 0 R ∧ g (ρ - c) = 0} := by
      intro ρ hρ
      rcases hρ with ⟨hzero, hdist⟩
      have hball : ρ - c ∈ Metric.closedBall 0 R := by
        simpa [Metric.mem_closedBall, Complex.dist_eq, c, sub_eq_add_neg] using hdist
      have hρne1 : (ρ : ℂ) ≠ 1 := by
        intro hρ1
        have hz1_ne : riemannZeta (1 : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
        exact hz1_ne (by simpa [hρ1] using! hzero)
      have hsum : (ρ - c) + c = ρ := by simp [sub_add_cancel]
      have hxne : (ρ - c) + c ≠ (1 : ℂ) := by simpa [hsum] using hρne1
      have hform : g (ρ - c) = (ρ - 1) * riemannZeta ρ := by
        simp [g, H, hsum, Function.update_of_ne hxne]
                                                   
      have hzeroζ : riemannZeta ρ = 0 := hzero
      have hzero' : g (ρ - c) = 0 := by
        calc
          g (ρ - c) = (ρ - 1) * riemannZeta ρ := hform
          _ = (ρ - 1) * 0 := by simp [hzeroζ]
          _ = 0 := by simp
      exact ⟨hball, hzero'⟩
                            
    have hg_diff : Differentiable ℂ g := by
      intro z
      have hH := hH_diff (z + c)
      have h_addc : DifferentiableAt ℂ (fun z : ℂ => z + c) z :=
        (differentiableAt_id.add_const c)
      simpa [g] using! hH.comp z h_addc
    have hg_analyticNhd_univ : AnalyticOnNhd ℂ g Set.univ :=
      (Complex.analyticOnNhd_univ_iff_differentiable).2 hg_diff
    have hg_analyticNhd : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) :=
      AnalyticOnNhd.mono hg_analyticNhd_univ (by intro z hz; simp)
    have hNonzero : ∃ z ∈ Metric.ball (0 : ℂ) 1, g z ≠ 0 := by
      rcases hg_nonzero with ⟨z, hz_in, hz_ne⟩
      have hz_in' : z ∈ Metric.ball (0 : ℂ) 1 := by
        have hRle : (R : ℝ) ≤ 1 := by norm_num
        exact Metric.ball_subset_ball hRle hz_in
      exact ⟨z, hz_in', hz_ne⟩
    have hfiniteKg : Set.Finite Kg :=
      (lem_Contra_finiteKR R hRpos (by norm_num : R < 1) g hg_analyticNhd hNonzero)
    have hTarget_eq : {ρ : ℂ | (ρ - c) ∈ Metric.closedBall 0 R ∧ g (ρ - c) = 0} =
          (fun ρ : ℂ => ρ + c) '' Kg := by
      ext ρ; constructor
      · intro h
        rcases h with ⟨hball, hzero⟩
        refine ⟨ρ - c, ⟨?_, ?_⟩, ?_⟩
        · exact hball
        · exact hzero
        · simp [sub_add_cancel]
      · intro h
        rcases h with ⟨z, ⟨hzball, hz0⟩, rfl⟩
        constructor
        · simpa [sub_add_cancel] using hzball
        · simpa [sub_add_cancel] using hz0
    have hTarget_fin : Set.Finite {ρ : ℂ | (ρ - c) ∈ Metric.closedBall 0 R ∧ g (ρ - c) = 0} := by
      have himg : Set.Finite ((fun ρ : ℂ => ρ + c) '' Kg) := hfiniteKg.image _
      exact hTarget_eq ▸ himg
    exact Set.Finite.subset hTarget_fin h_subset

lemma lem_Re1zge0 (z : ℂ) : z.re > 0 → (1 / z).re > 0 := by
  intro h
                          
  have hz_ne_zero : z ≠ 0 := by
    intro hz_eq_zero
    rw [hz_eq_zero] at h
    simp at h
                                
  rw [one_div]
                                               
  rw [Complex.inv_re]
                                                                                                     
  apply div_pos h
                             
  rwa [Complex.normSq_pos]

lemma lem_sigmage1 (sigma t : ℝ) (hsigma : sigma > 1) : riemannZeta (sigma + t * Complex.I) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_le_re
  simp [Complex.add_re, Complex.mul_re, Complex.I_re]
  linarith

lemma lem_sigmale1 (sigma1 t1 : ℝ) : riemannZeta (sigma1 + t1 * Complex.I) = 0 → sigma1 ≤ 1 := by
  intro h
                                       
  by_contra h_not_le
                                                   
  push Not at h_not_le
                                                                             
  have h_nonzero := lem_sigmage1 sigma1 t1 h_not_le
                                                              
  exact h_nonzero h

lemma lem_sigmale1Zt (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) : rho1.re ≤ 1 := by
                                                                    
  have h1 : rho1 ∈ zeroZ := h_rho1_in_Zt.1
                                                                  
  have h2 : riemannZeta rho1 = 0 := h1
                                                       
  have h3 : rho1 = rho1.re + rho1.im * Complex.I := by simp [Complex.re_add_im]
                                         
  rw [h3] at h2
                           
  exact lem_sigmale1 rho1.re rho1.im h2

lemma complex_abs_of_real (x : ℝ) : ‖(x : ℂ)‖ = abs x := by
  rw [Complex.norm_real, Real.norm_eq_abs]

lemma center_eq_comm (t : ℝ) :
  ((3/2 : ℂ) + (Complex.I : ℂ) * (t : ℂ)) = ((3/2 : ℂ) + (t : ℂ) * Complex.I) := by
  have h : (Complex.I : ℂ) * (t : ℂ) = (t : ℂ) * Complex.I := by
    simpa using mul_comm (Complex.I : ℂ) (t : ℂ)
  simp [h]

lemma lem_Realsum {α : Type*} (s : Finset α) (f : α → ℂ) : (Finset.sum s f).re = Finset.sum s (fun i => (f i).re) := by
  exact Complex.re_sum s f

lemma lem_sumrho1 (t : ℝ) (δ : ℝ) (_hdelta_pos : δ > 0) (_hdelta_lt1 : δ < 1) :
    (Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t))
        (fun rho1 : ℂ =>
                    ((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
                      (((1 : ℂ) + δ + t * Complex.I) - rho1))).re =
    Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t))
    (fun rho1 : ℂ =>
                    (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
                      (((1 : ℂ) + δ + t * Complex.I) - rho1)).re) := by
  exact lem_Realsum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t)) _

lemma lem_1deltatrho1 (delta : ℝ) (_hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (_h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :    ((1 : ℂ) + delta + t * Complex.I - rho1) = ((1 : ℝ) + delta - rho1.re) + (t - rho1.im) * Complex.I := by
                                                           
  conv_lhs => rw [← Complex.re_add_im rho1]

  simp only [sub_add_eq_sub_sub]
                                                      
  ring_nf
                                                               
  simp only [Complex.ofReal_one]
  ring

lemma lem_Re1deltatrho1 (delta : ℝ) (hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :
((1 : ℂ) + delta + t * Complex.I - rho1).re = (1 : ℝ) + delta - rho1.re := by
                                                   
  rw [lem_1deltatrho1 delta hdelta t rho1 h_rho1_in_Zt]

  rw [Complex.add_re]
                                      
  rw [Complex.mul_I_re]
             
  simp

lemma lem_Re1delta1 (delta : ℝ) (_hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :
(1 : ℝ) + delta - rho1.re ≥ delta := by
                                            
  have h_rho1_re_le_1 : rho1.re ≤ 1 := lem_sigmale1Zt t rho1 h_rho1_in_Zt
                               
  have h_nonneg : 1 - rho1.re ≥ 0 := by linarith
                                                                              
  linarith

lemma lem_Re1deltatge (delta : ℝ) (hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :    ((1 : ℂ) + delta + t * Complex.I - rho1).re ≥ delta := by
                                                     
  rw [lem_Re1deltatrho1 delta hdelta t rho1 h_rho1_in_Zt]
                                                      
  exact lem_Re1delta1 delta hdelta t rho1 h_rho1_in_Zt

lemma lem_Re1deltatneq0 (delta : ℝ) (hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :
((1 : ℂ) + delta + t * Complex.I - rho1).re > 0 := by
                                                               
  have h_ge_delta : ((1 : ℂ) + delta + t * Complex.I - rho1).re ≥ delta := lem_Re1deltatge delta hdelta t rho1 h_rho1_in_Zt
                                                                         
  linarith [hdelta]

lemma lem_Re1deltatge0 (delta : ℝ) (hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :
(1 / ((1 : ℂ) + delta + t * Complex.I - rho1)).re ≥ 0 := by
                                                                      
  apply le_of_lt
  apply lem_Re1zge0
                                                          
  exact lem_Re1deltatneq0 delta hdelta t rho1 h_rho1_in_Zt

lemma lem_Re1deltatge0m (delta : ℝ) (hdelta : delta > 0) (t : ℝ) (_hdelta_lt_1 : delta < 1)
  (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :
  (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
    (((1 : ℂ) + delta + t * Complex.I) - rho1)).re ≥ 0 := by
                                                     
  let n := (analyticOrderAt riemannZeta rho1).toNat
  let z := ((1 : ℂ) + delta + t * Complex.I) - rho1

  have h_eq : (n : ℂ) / z = n • (1/z) := by
    rw [nsmul_eq_mul]
    simp [div_eq_mul_inv]

  rw [h_eq, Complex.re_nsmul]

  apply nsmul_nonneg
  exact lem_Re1deltatge0 delta hdelta t rho1 h_rho1_in_Zt

lemma lem_Z1split (delta : ℝ) (_hdelta : delta > 0) (_hdelta_lt1 : delta < 1) (rho : ℂ)
  (_h_rho_in_zeroZ : rho ∈ zeroZ)
  (h_rho_in_Zt : rho ∈ ZetaZerosNearPoint rho.im) :
    Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im))
      (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re) =
    (((analyticOrderAt riemannZeta rho).toNat : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho)).re +
    Finset.sum ((Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im)).erase rho)
      (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re) := by
  classical
  set s := Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im)
  set f := fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re
  have hmem : rho ∈ s := by
    simpa [s, Set.Finite.mem_toFinset (ZetaZerosNearPoint_finite rho.im)] using h_rho_in_Zt
                                                            
  have h_decomp : ∑ x ∈ s, f x = f rho + ∑ x ∈ s.erase rho, f x := by
    rw [← Finset.insert_erase hmem]
    rw [Finset.sum_insert (Finset.notMem_erase rho s)]
    simp
  exact h_decomp

lemma re_ofReal_div_ge_one (a : ℝ) (z : ℂ) (ha : 1 ≤ a) (hz : 0 ≤ (1 / z).re) : ((a : ℂ) / z).re ≥ (1 / z).re := by
  have hrepr : ((a : ℂ) / z).re = a * (1 / z).re := by
    simp [div_eq_mul_inv, Complex.mul_re]
  have hmul : (1 : ℝ) * (1 / z).re ≤ a * (1 / z).re :=
    mul_le_mul_of_nonneg_right ha hz
  calc
    ((a : ℂ) / z).re = a * (1 / z).re := hrepr
    _ ≥ 1 * (1 / z).re := by exact hmul
    _ = (1 / z).re := by simp [one_mul]

lemma analyticAt_riemannZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
                                                                  
  refine (Complex.analyticAt_iff_eventually_differentiableAt).2 ?_
                                                                                          
  filter_upwards [eventually_ne_nhds hs] with z hz
  exact differentiableAt_riemannZeta hz

lemma riemannZeta_not_eventually_zero_of_ne_one {s : ℂ} (hs : s ≠ 1) :
  ¬ (∀ᶠ z in nhds s, riemannZeta z = 0) := by
  intro hEvZero
                                                                                            
  let H : ℂ → ℂ := Function.update (fun z : ℂ => (z - 1) * riemannZeta z) 1 1
                                                    
  have hH_diff : Differentiable ℂ H := by
    intro z
    rcases eq_or_ne z 1 with rfl | hz
    ·                                   
      refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
      ·                                                 
                                                                 
        filter_upwards [self_mem_nhdsWithin] with t ht
        have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) t := (differentiableAt_id.sub_const 1)
        have h2 : DifferentiableAt ℂ riemannZeta t := by
                                               
          exact differentiableAt_riemannZeta ht
        have hdiff := h1.mul h2
                                                           
        apply hdiff.congr_of_eventuallyEq
        filter_upwards [eventually_ne_nhds ht] with u hu
        simp [H, Function.update_of_ne hu]
      ·                                        
        simpa [H, continuousAt_update_same] using riemannZeta_residue_one
    ·                                     
      have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) z := (differentiableAt_id.sub_const 1)
      have h2 : DifferentiableAt ℂ riemannZeta z := by
        exact differentiableAt_riemannZeta hz
      have hdiff := h1.mul h2
                                                      
      apply hdiff.congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hz] with u hu
      simp [H, Function.update_of_ne hu]
                                                                            
  have hH_analytic : AnalyticOnNhd ℂ H Set.univ :=
    (Complex.analyticOnNhd_univ_iff_differentiable).2 hH_diff
                                             
  have h0_analytic : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) Set.univ := by
    intro z _; simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) z)
                                                                                         
  have hEv_ne1 : ∀ᶠ z in nhds s, z ≠ 1 := eventually_ne_nhds hs
  have hEv_H0 : ∀ᶠ z in nhds s, H z = 0 := by
    filter_upwards [hEvZero, hEv_ne1] with z hz_zero hz_ne1
                                        
    have : H z = (z - 1) * riemannZeta z := by simp [H, Function.update_of_ne hz_ne1]
    simp [this, hz_zero]
                                                                              
  have hEqOn : Set.EqOn H (fun _ : ℂ => (0 : ℂ)) Set.univ := by
                           
    have hU : IsPreconnected (Set.univ : Set ℂ) := by simpa using isPreconnected_univ
    exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hH_analytic h0_analytic hU (by simp) hEv_H0
  have hHeq : H = fun _ : ℂ => (0 : ℂ) := by
    funext z; simpa using hEqOn (by simp : z ∈ (Set.univ : Set ℂ))
                                         
  have h2ne1 : (2 : ℂ) ≠ 1 := by norm_num
  have hH2 : H (2 : ℂ) = (2 - 1) * riemannZeta (2 : ℂ) := by
    simp [H]
  have hzeta2_ne : riemannZeta (2 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp)
  have hprod_zero' : 0 = (2 - 1) * riemannZeta (2 : ℂ) := by
    simpa [hHeq] using hH2
  have hprod_zero : (2 - 1) * riemannZeta (2 : ℂ) = 0 := hprod_zero'.symm
  have hnonzero : (2 - 1) * riemannZeta (2 : ℂ) ≠ 0 := by
    have hcoeff : (2 : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr h2ne1
    exact mul_ne_zero hcoeff hzeta2_ne
  exact hnonzero hprod_zero

lemma analyticOrderAt_pos_toNat_of_zero_of_analytic_not_eventually_zero {f : ℂ → ℂ} {z0 : ℂ}
  (hf : AnalyticAt ℂ f z0) (hzero : f z0 = 0)
  (hnot : ¬ (∀ᶠ z in nhds z0, f z = 0)) :
  1 ≤ (analyticOrderAt f z0).toNat := by
  classical
                                                 
  have hne0 : analyticOrderAt f z0 ≠ 0 := by
    intro h0
    have hzne : f z0 ≠ 0 := (AnalyticAt.analyticOrderAt_eq_zero hf).1 h0
    exact hzne hzero
                                                                         
  have hneTop : analyticOrderAt f z0 ≠ ⊤ := by
    intro htop
    have hall : (∀ᶠ z in nhds z0, f z = 0) := (analyticOrderAt_eq_top).1 htop
    exact hnot hall
                                          
  rcases WithTop.ne_top_iff_exists.mp hneTop with ⟨n, hn⟩
                             
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    apply hne0
                                            
    simp [hn.symm, hn0]
    rfl
                    
  have hposn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn_ne_zero)
                                         
  simpa [hn.symm] using! hposn

lemma lem_Z1splitge (delta : ℝ) (hdelta_pos : delta > 0) (hdelta : delta < 1) (rho : ℂ)
  (h_rho_in_zeroZ : rho ∈ zeroZ) (h_rho_in_Zt : rho ∈ ZetaZerosNearPoint rho.im) :
    Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im)) (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re) ≥
(1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho)).re := by
  classical
                           
  have hsplit :=
    lem_Z1split delta hdelta_pos hdelta rho h_rho_in_zeroZ h_rho_in_Zt
                                    
  rw [hsplit]
                                       
  have h_rho_ne_one : rho ≠ (1 : ℂ) := by
    intro h
    have hz1_ne : riemannZeta (1 : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
    exact hz1_ne (by simpa [h] using! h_rho_in_zeroZ)
  have hAnal : AnalyticAt ℂ riemannZeta rho := analyticAt_riemannZeta_of_ne_one h_rho_ne_one
  have hNotEv : ¬ (∀ᶠ z in nhds rho, riemannZeta z = 0) :=
    riemannZeta_not_eventually_zero_of_ne_one h_rho_ne_one
  have horder_nat : 1 ≤ (analyticOrderAt riemannZeta rho).toNat :=
    analyticOrderAt_pos_toNat_of_zero_of_analytic_not_eventually_zero
      hAnal (by simpa using! h_rho_in_zeroZ) hNotEv
  have ha_real : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta rho).toNat : ℝ) := by exact_mod_cast horder_nat
  have hz_nonneg : 0 ≤ (1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho)).re :=
    lem_Re1deltatge0 delta hdelta_pos rho.im rho h_rho_in_Zt
  have hfirst :
      (1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho)).re
        ≤ (((((analyticOrderAt riemannZeta rho).toNat : ℝ) : ℂ) /
            (((1 : ℂ) + delta + rho.im * Complex.I) - rho))).re := by
                               
    simpa [ge_iff_le] using
      (re_ofReal_div_ge_one ((analyticOrderAt riemannZeta rho).toNat : ℝ)
        ((((1 : ℂ) + delta + rho.im * Complex.I) - rho)) ha_real hz_nonneg)
                                        
  have hsum_nonneg :
      0 ≤ Finset.sum
        ((Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im)).erase rho)
        (fun rho1 : ℂ =>
          (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
            (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re) := by
    apply Finset.sum_nonneg
    intro rho1 hmem
    rcases Finset.mem_erase.mp hmem with ⟨_, hmemS⟩
                                     
    have hZt : rho1 ∈ ZetaZerosNearPoint rho.im := by
      simpa [Set.Finite.mem_toFinset (ZetaZerosNearPoint_finite rho.im)] using hmemS
                    
    have hne1 : rho1 ≠ (1 : ℂ) := by
      intro h
      have hz1_ne : riemannZeta (1 : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
      have hzero1 : riemannZeta rho1 = 0 := hZt.1
      exact hz1_ne (by simpa [h] using hzero1)
                           
    have hAnal1 : AnalyticAt ℂ riemannZeta rho1 := analyticAt_riemannZeta_of_ne_one hne1
    have hNotEv1 : ¬ (∀ᶠ z in nhds rho1, riemannZeta z = 0) :=
      riemannZeta_not_eventually_zero_of_ne_one hne1
    have hzero1 : riemannZeta rho1 = 0 := hZt.1
    have horder1 : 1 ≤ (analyticOrderAt riemannZeta rho1).toNat :=
      analyticOrderAt_pos_toNat_of_zero_of_analytic_not_eventually_zero hAnal1 hzero1 hNotEv1
    have ha1_real : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta rho1).toNat : ℝ) := by exact_mod_cast horder1
                       
    have hz1_nonneg : 0 ≤ (1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re :=
      lem_Re1deltatge0 delta hdelta_pos rho.im rho1 hZt
                                           
    have hge :
        (1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re ≤
          (((((analyticOrderAt riemannZeta rho1).toNat : ℝ) : ℂ) /
            (((1 : ℂ) + delta + rho.im * Complex.I) - rho1))).re := by
      simpa [ge_iff_le] using
        (re_ofReal_div_ge_one ((analyticOrderAt riemannZeta rho1).toNat : ℝ)
          ((((1 : ℂ) + delta + rho.im * Complex.I) - rho1)) ha1_real hz1_nonneg)
                                                       
    exact le_trans hz1_nonneg hge
                           
  have h := add_le_add hfirst hsum_nonneg
                             
  simpa using h

lemma lem_1deltatrho0 (delta : ℝ) (_hdelta : delta > 0) (rho : ℂ) (_h_rho_in_zeroZ : rho ∈ zeroZ) :
((1 : ℂ) + delta + rho.im * Complex.I - rho) = ((1 : ℝ) + delta - rho.re) := by

  calc (1 : ℂ) + delta + rho.im * Complex.I - rho
    = (1 : ℂ) + delta + rho.im * Complex.I - (rho.re + rho.im * Complex.I) := by rw [Complex.re_add_im]
  _ = (1 : ℂ) + delta - rho.re := by ring
  _ = ((1 : ℝ) + delta - rho.re : ℂ) := by norm_cast

lemma lem_1delsigReal2 (delta : ℝ) (_hdelta : delta > 0) (rho : ℂ) (_h_rho_in_zeroZ : rho ∈ zeroZ) :
(1 / ((1 : ℂ) + delta - rho.re)).re = 1 / ((1 : ℝ) + delta - rho.re) := by
                                                                           
  have h_eq : (1 : ℂ) + delta - rho.re = (1 + delta - rho.re : ℝ) := by
    simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_one]

  rw [h_eq]

  rw [Complex.div_ofReal_re]

  rw [Complex.one_re]

lemma lem_re_inv_one_plus_delta_minus_rho_real (delta : ℝ) (hdelta : delta > 0)  (rho : ℂ) (h_rho_in_zeroZ : rho ∈ zeroZ) :
(1 / ((1 : ℂ) + delta + rho.im * Complex.I - rho)).re = 1 / ((1 : ℝ) + delta - rho.re) := by
                                                      
  rw [lem_1deltatrho0 delta hdelta rho h_rho_in_zeroZ]
                               
  exact lem_1delsigReal2 delta hdelta rho h_rho_in_zeroZ

lemma lem_Z1splitge2 (delta : ℝ) (hdelta : delta > 0) (hdelta_lt_1 : delta < 1) (rho : ℂ)
  (h_rho_in_zeroZ : rho ∈ zeroZ) (h_rho_in_Zt : rho ∈ ZetaZerosNearPoint rho.im) :
    Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im))
      (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / ((1 : ℂ) + delta + rho.im * Complex.I - rho1)).re) ≥
1 / ((1 : ℝ) + delta - rho.re) := by
                                                    
  have h1 := lem_Z1splitge delta hdelta hdelta_lt_1 rho h_rho_in_zeroZ h_rho_in_Zt
                                                                                  
  have h2 := lem_re_inv_one_plus_delta_minus_rho_real delta hdelta rho h_rho_in_zeroZ
                        
  rw [← h2]
  exact h1

lemma lem_Z1splitge3 (delta : ℝ) (hdelta : delta > 0) (hdelta_lt_1 : delta < 1) (sigma t : ℝ) (rho : ℂ)
  (h_rho_eq : rho = sigma + t * Complex.I) (h_rho_in_zeroZ : rho ∈ zeroZ)
  (h_rho_in_Zt : rho ∈ ZetaZerosNearPoint t) :
(Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t)) (fun rho1 : ℂ => ((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + t * Complex.I) - rho1)) ).re ≥ 1 / ((1 : ℝ) + delta - sigma) := by
                                                                                   
  rw [lem_sumrho1 t delta hdelta hdelta_lt_1]

  have h_rho_im : rho.im = t := by
    rw [h_rho_eq]
    simp [Complex.add_im, Complex.mul_im, Complex.I_im]
  have h_rho_re : rho.re = sigma := by
    rw [h_rho_eq]
    simp [Complex.add_re, Complex.mul_re, Complex.I_re]

  have h_rho_in_Zt' : rho ∈ ZetaZerosNearPoint rho.im := by
    rw [h_rho_im]
    exact h_rho_in_Zt

  have h_bound := lem_Z1splitge2 delta hdelta hdelta_lt_1 rho h_rho_in_zeroZ h_rho_in_Zt'

  convert (preTransparency := .instances) h_bound using 1
                                                       
  simp_rw [← h_rho_im]
                                                             
  rw [h_rho_re]

lemma neg_logDeriv_zeta_eq_vonMangoldt_sum (s : ℂ) (hs : 1 < s.re) : -(deriv riemannZeta s / riemannZeta s) = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-s) := by
                                                                                     
  have h1 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

  have h2 : -deriv riemannZeta s / riemannZeta s = LSeries (fun n => ↑(ArithmeticFunction.vonMangoldt n)) s := h1.symm
                                                                                                                 
  have h3 : -(deriv riemannZeta s / riemannZeta s) = -deriv riemannZeta s / riemannZeta s := by ring
  rw [h3, h2]

  rw [LSeries]
  congr 1
  ext n
  rw [LSeries.term_def]
  split_ifs with h_zero
  ·                                
    simp [h_zero]
  ·                                                                     
    rw [div_eq_mul_inv, Complex.cpow_neg]

lemma zeta1zetaseries {s : ℂ} (hs : 1 < s.re) :
-logDerivZeta s = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-s) := by
  unfold logDerivZeta
                                                                                                                       
  exact neg_logDeriv_zeta_eq_vonMangoldt_sum s hs

lemma zeta1zetaseriesxy (x y : ℝ) (hx : 1 < x) :
    -logDerivZeta (x + y * I) = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I)) := by
  apply zeta1zetaseries

  have h : (x + y * I).re = x := by
    simp [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im]
    right
    exact Complex.I_re
  rw [h]
  exact hx

lemma Zconverges1 (x y : ℝ) (hx : 1 < x) : riemannZeta (x + y * I) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_lt_re

  have h : (x + y * I).re = x := by
    rw [Complex.add_re, Complex.ofReal_re]
    simp [Complex.mul_re]
    right
    exact Complex.I_re
  rw [h]
  exact hx

lemma complex_re_of_real_add_imag (x y : ℝ) : (x + y * I).re = x := by
  simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im]
                                                                           
  right
  exact Complex.I_re

lemma vonMangoldt_LSeriesSummable (s : ℂ) (hs : 1 < s.re) : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
                                                                            
  exact ArithmeticFunction.LSeriesSummable_vonMangoldt hs

lemma summable_of_support_singleton {α : Type*} [SeminormedAddCommGroup α] (f : ℕ → α) (n₀ : ℕ) (h : ∀ n : ℕ, n ≠ n₀ → f n = 0) : Summable f := by
                                                     
  have h_finite_support : Set.Finite (Function.support f) := by
                                       
    have h_subset : Function.support f ⊆ {n₀} := by
      intro n hn

      by_contra h_ne
                                                 
      have h_zero : f n = 0 := h n h_ne
                                     
      simp [Function.mem_support] at hn
      exact hn h_zero
                                                                 
    exact Set.Finite.subset (Set.finite_singleton n₀) h_subset

  exact summable_of_hasFiniteSupport h_finite_support

lemma summable_of_summable_add_sub {α : Type*} [SeminormedAddCommGroup α] (f g h : ℕ → α) (h_eq : f = g + h) (hf : Summable f) (hh : Summable h) : Summable g := by

  have g_eq_f_sub_h : g = f - h := by
                                           
    rw [← sub_eq_iff_eq_add] at h_eq
    exact h_eq.symm

  rw [g_eq_f_sub_h]

  exact hf.sub hh

lemma LSeriesSummable_to_summable (f : ℕ → ℂ) (s : ℂ) (h : LSeriesSummable f s) : Summable (fun n => f n * (n : ℂ) ^ (-s)) := by
                                                          
  have h_term_summable : Summable (LSeries.term f s) := h

  have h_eq_nonzero : ∀ n : ℕ, n ≠ 0 → LSeries.term f s n = f n * (n : ℂ) ^ (-s) := by
    intro n hn
    rw [LSeries.term_of_ne_zero hn]
    rw [div_eq_mul_inv, Complex.cpow_neg]

  let diff := fun n => LSeries.term f s n - f n * (n : ℂ) ^ (-s)

  have h_diff_support : ∀ n : ℕ, n ≠ 0 → diff n = 0 := by
    intro n hn
    simp only [diff]
    rw [h_eq_nonzero n hn]
    simp

  have h_diff_summable : Summable diff := by
                                              
    apply summable_of_support_singleton diff 0 h_diff_support

  have h_rw : LSeries.term f s = (fun n => f n * (n : ℂ) ^ (-s)) + diff := by
    ext n
    simp only [diff, Pi.add_apply]
    ring

  exact summable_of_summable_add_sub (LSeries.term f s) (fun n => f n * (n : ℂ) ^ (-s)) diff h_rw h_term_summable h_diff_summable

lemma ReZconverges1 (x y : ℝ) (hx : 1 < x) :
Summable (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re) := by
                                                                                                
  have h_nonzero : riemannZeta (x + y * I) ≠ 0 := Zconverges1 x y hx

  have h_re_gt_one : 1 < (x + y * I).re := by
    rw [complex_re_of_real_add_imag]
    exact hx

  have h_L_summable : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) :=
    vonMangoldt_LSeriesSummable (x + y * I) h_re_gt_one

  have h_summable : Summable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))) :=
    LSeriesSummable_to_summable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) h_L_summable

  have h_hasSum : HasSum (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))) (∑' n, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))) :=
    h_summable.hasSum

  have h_hasSum_re : HasSum (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))).re) (∑' n, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))).re :=
    Complex.hasSum_re h_hasSum

  exact h_hasSum_re.summable

lemma lem_nxy (n : ℕ) (hn : n ≥ 1) (x y : ℝ) :
    Complex.cpow (n : ℂ) (-(x + y * I)) = Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I)) := by
                                              
  have h : -(x + y * I) = (-x : ℂ) + (-(y * I)) := by ring
  rw [h]
                                                         
  exact lem_exprule n hn (-x : ℂ) (-(y * I))

lemma lem_zeta1zetaseriesxy2 (x y : ℝ) (hx : 1 < x) :
    -logDerivZeta (x + y * I) = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * (Complex.cpow (n : ℂ) ((-x) : ℂ)) * (Complex.cpow (n : ℂ) (-(y * I))) := by
                            
  rw [zeta1zetaseriesxy x y hx]
                                             
  congr 1
  ext n
                      
  rw [← Complex.cpow_eq_pow]
                                                          
  by_cases h : n = 0
  ·                                
    simp [h]
  ·                                 
    have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    rw [lem_nxy n hn x y]
                                                          
    ring

lemma complex_add_re_ofReal_mul_I (x y : ℝ) : (x + y * I).re = x := by
  rw [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
                                  
  have h : I.re = 0 := Complex.I_re
  rw [h]
  simp

lemma LSeriesSummable_to_explicit_summable (x y : ℝ) (_hx : 1 < x) : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) → Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))) := by
  intro h_summable

  have h_vm_zero : (ArithmeticFunction.vonMangoldt 0 : ℂ) = 0 := by
    simp

  have h_eq : ∀ n : ℕ, LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) n =
    (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I)) := by
    intro n
                                                     
    rw [LSeries.term_def₀ h_vm_zero]

    rw [← Complex.cpow_eq_pow]

    by_cases hn : n = 0
    ·                                
      simp [hn]
    ·                                    
      have hn_ge : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn
      rw [lem_nxy n hn_ge x y]
      ring

  have h_term_summable : Summable (fun n => LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) n) := by
    exact h_summable

  convert (preTransparency := .instances) h_term_summable using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  exact (h_eq n).symm

lemma Zseriesconverges1 (x y : ℝ) (hx : 1 < x) :
Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))) := by
                                                        
  have h_zeta_ne_zero := Zconverges1 x y hx

  have h_series := lem_zeta1zetaseriesxy2 x y hx

  have h_re : 1 < (x + y * I).re := by
    rw [complex_add_re_ofReal_mul_I]
    exact hx

  have h_summable := ArithmeticFunction.LSeriesSummable_vonMangoldt h_re

  exact LSeriesSummable_to_explicit_summable x y hx h_summable

lemma sumRealLambda (x y : ℝ) (hx : 1 < x) :
    (∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))).re =
    ∑' (n : ℕ), ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))).re := by
  apply Complex.re_tsum
  exact Zseriesconverges1 x y hx

lemma lem_sumRealZ (x y : ℝ) (hx : 1 < x) :
    (-logDerivZeta (x + y * I)).re = ∑' (n : ℕ), ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))).re := by
                                                         
  rw [lem_zeta1zetaseriesxy2 x y hx]
                                                   
  exact sumRealLambda x y hx

lemma complex_cpow_neg_real (n : ℕ) (x : ℝ) (_hn : n ≥ 1) : Complex.cpow (n : ℂ) ((-x) : ℂ) = Complex.ofReal ((n : ℝ) ^ (-x)) := by
                                     
  have h_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
                                   
  rw [Complex.cpow_eq_pow]
                                                   
  rw [Complex.ofReal_cpow h_nonneg (-x)]
                                          
  congr 1
                                 
  simp

lemma RealLambdaxy (n : ℕ) (x y : ℝ) (hn : n ≥ 1) (_hx : 1 < x) :
    ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))).re =
((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) * (Complex.cpow (n : ℂ) (-(y * I))).re := by
                                                              
  let b := ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-x)

  have h1 : (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) = (b : ℂ) := by
                                                
    have h_real_pow : Complex.cpow (n : ℂ) ((-x) : ℂ) = Complex.ofReal ((n : ℝ) ^ (-x)) := by
      exact complex_cpow_neg_real n x hn

    rw [h_real_pow]
    rw [← Complex.ofReal_mul]

  have h2 : (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I)) =
           ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ)) * Complex.cpow (n : ℂ) (-(y * I)) := by
    rw [mul_assoc]

  rw [h2, h1]

  exact lem_realbw b (Complex.cpow (n : ℂ) (-(y * I)))

lemma ReZseriesRen (x y : ℝ) (hx : 1 < x) :
    (-logDerivZeta (x + y * I)).re = ∑' (n : ℕ), ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) * (Complex.cpow (n : ℂ) (-(y * I))).re := by
  rw [lem_sumRealZ x y hx]
  congr 1
  ext n
  by_cases h : n = 0
  · simp [h]
  · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    exact RealLambdaxy n x y hn hx

lemma Rezeta1zetaseries (x y : ℝ) (hx : 1 < x) :
    (-logDerivZeta (x + y * I)).re = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ)) := by
  rw [ReZseriesRen x y hx]
  congr 1
  ext n
  by_cases h : n = 0
  · simp [h]
  · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    rw [← lem_eacosalog3 n hn y]
                                                                                          
    congr 1
                                                                        
    rw [Complex.cpow_eq_pow]
                                     
    simp [I]

lemma complex_vonMangoldt_real_part_eq (n : ℕ) (x y : ℝ) (hn : n ≥ 1) (hx : 1 < x) :
((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re =
(ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ)) := by
                                                   
  rw [lem_nxy n hn x y]

  rw [← mul_assoc]

  rw [RealLambdaxy n x y hn hx]

  have h_cpow : (Complex.cpow (n : ℂ) (-(y * I))).re = ((n : ℂ) ^ (-(y * I))).re := by
    rw [Complex.cpow_eq_pow]

  have h_I : -(y * I) = -y * Complex.I := by
    simp [I]

  rw [h_cpow, h_I]

  rw [lem_eacosalog3 n hn y]

lemma Rezetaseries_convergence (x y : ℝ) (hx : 1 < x) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ))) := by
                                                                           
  have h1 : Summable (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re) :=
    ReZconverges1 x y hx

  have h2 : ∀ n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re =
                      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ)) := by
    intro n
    by_cases h : n = 0
    · simp [h]
    · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
      exact complex_vonMangoldt_real_part_eq n x y hn hx

  have h3 : (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re) =
            (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ))) :=
    funext h2
  rwa [← h3]

lemma Rezetaseries2t (x t : ℝ) (hx : 1 < x) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (2 * t * Real.log (n : ℝ))) := by
                                                  
  exact Rezetaseries_convergence x (2 * t) hx

lemma lem_cost0 (n : ℕ) (_hn : n ≥ 1) (t : ℝ) (ht : t = 0) : Real.cos (t * Real.log (n : ℝ)) = 1 := by
  rw [ht]
  simp

lemma Rezetaseries0 (x : ℝ) (hx : 1 < x) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) := by
                                              
  have h1 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (0 * Real.log (n : ℝ))) :=
    Rezetaseries_convergence x 0 hx
                                             
  convert (preTransparency := .instances) h1 using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  by_cases h : n = 0
  · simp [h]
  · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    rw [lem_cost0 n hn 0 rfl]
    ring

lemma uniform_bound_Z0_complex : ∃ δ0 > 0, ∃ C0 ≥ 0, ∀ δ : ℝ, 0 < δ → δ < δ0 → ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C0 := by
                                             
  let f : ℝ → ℂ := fun δ => -logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))
                                           
  have hO := Z0bound
                                                                 
  rcases (Asymptotics.isBigO_iff).1 hO with ⟨c, hc⟩
  have h_event : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ‖f δ‖ ≤ c := by
                             
    have : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ‖f δ‖ ≤ c * ‖(1 : ℂ)‖ := hc
    refine this.mono ?_
    intro δ hδ
    have : ‖(1 : ℂ)‖ = (1 : ℝ) := by simp
    simpa [this] using hδ
                                                                                 
  rcases (Filter.eventually_iff_exists_mem).1 h_event with ⟨S, hS_in, hS_bound⟩
                                                                   
  rcases (mem_nhdsGT_iff_exists_Ioc_subset).1 hS_in with ⟨δ0, hδ0pos, hIoc_sub_S⟩
                                                                       
  refine ⟨δ0, hδ0pos, max c 0, le_max_right _ _, ?_⟩
  intro δ hδpos hδlt
                             
  have hδ_in_S : δ ∈ S := hIoc_sub_S ⟨hδpos, le_of_lt hδlt⟩
                                        
  have hnorm_le_c : ‖f δ‖ ≤ c := hS_bound δ hδ_in_S
                                                      
  exact le_trans hnorm_le_c (le_max_left _ _)

lemma tsum_nonneg_of_nonneg {f : ℕ → ℝ} (hnon : ∀ n, 0 ≤ f n) : 0 ≤ ∑' n, f n := by
  simpa using (tsum_nonneg hnon)

lemma vonMangoldt_rpow_nonneg (x : ℝ) : ∀ n, 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) := by
  intro n
  have h1 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  have h2 : 0 ≤ (n : ℝ) ^ (-x) := by
    exact Real.rpow_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n) _
  simpa using mul_nonneg h1 h2

lemma norm_negLogDerivZeta_real_eq_abs_tsum_vonMangoldt (x : ℝ) (hx : 1 < x) :
  ‖-logDerivZeta (x : ℂ)‖ = |∑' n, ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x))| := by
                                                    
  have hx' : 1 < (x : ℂ).re := by simpa using hx
  have hseries := zeta1zetaseries (s := (x : ℂ)) hx'
                                                                                      
  let g : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)
  have hterm : ∀ n : ℕ,
      (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x : ℂ)) = (g n : ℂ) := by
    intro n
    by_cases h : n = 0
    ·                                               
      have hv0C : (ArithmeticFunction.vonMangoldt 0 : ℂ) = 0 := by
        simp
      have hv0R : (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 := by
        simp
      simp [g, h, hv0R]
    ·                                               
      have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
      have hcp : (n : ℂ) ^ (-(x : ℂ)) = Complex.ofReal ((n : ℝ) ^ (-x)) :=
        complex_cpow_neg_real n x hn
                                              
      have : (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x : ℂ))
              = Complex.ofReal (ArithmeticFunction.vonMangoldt n) * Complex.ofReal ((n : ℝ) ^ (-x)) := by
        simp [hcp]
      simpa [g, Complex.ofReal_mul] using this
                                                          
  have hsum_eq : (∑' n, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x : ℂ)))
                = ∑' n, (g n : ℂ) := by
                                             
    have hfun : (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x : ℂ)))
                = (fun n => (g n : ℂ)) := funext hterm
    simp [hfun]
                                                                     
  have hsum_ofReal : (∑' n, (g n : ℂ)) = Complex.ofReal (∑' n, g n) := by
    simpa using (Complex.ofReal_tsum g).symm
                                                                                               
  have hval : -logDerivZeta (x : ℂ) = Complex.ofReal (∑' n, g n) := by
                                         
    simpa [hsum_eq, hsum_ofReal] using hseries
                                                                            
  calc
    ‖-logDerivZeta (x : ℂ)‖ = ‖Complex.ofReal (∑' n, g n)‖ := by simp [hval]
    _ = |∑' n, g n| := by
      exact (RCLike.norm_ofReal (K := ℂ) (∑' n, g n))

lemma tsum_le_of_nonneg_of_le {f g : ℕ → ℝ} (hf : Summable f) (hg : Summable g) (_hnonneg : ∀ n, 0 ≤ f n) (hle : ∀ n, f n ≤ g n) : (∑' n, f n) ≤ (∑' n, g n) := by
  classical
  exact Summable.tsum_le_tsum hle hf hg

lemma rpow_neg_antitone {a x y : ℝ} (ha : 1 ≤ a) (hxy : x ≥ y) : a ^ (-x) ≤ a ^ (-y) := by

  simpa using (Real.rpow_le_rpow_of_exponent_le ha (neg_le_neg hxy))

lemma bounded_on_compact_interval (a b : ℝ) (h0 : 0 < a) (_hle : a ≤ b) : ∃ Cmid ≥ 0, ∀ δ : ℝ, a ≤ δ → δ ≤ b → ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ Cmid := by
                                      
  let s : Set ℝ := Set.Icc a b
  let f : ℝ → ℂ := fun δ => -logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))

  let H : ℂ → ℂ := Function.update (fun z : ℂ => (z - 1) * riemannZeta z) 1 1

  have hH_diff : Differentiable ℂ H := by
    intro z
    rcases eq_or_ne z 1 with rfl | hz
    ·                                                 
      refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
      ·                                                           
        filter_upwards [self_mem_nhdsWithin] with t ht
        have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - 1) * riemannZeta u) t := by
          have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) t :=
            (differentiableAt_id.sub_const 1)
          have h2 : DifferentiableAt ℂ riemannZeta t :=
            (differentiableAt_riemannZeta ht)
          exact h1.mul h2
        apply DifferentiableAt.congr_of_eventuallyEq hdiff
        filter_upwards [eventually_ne_nhds ht] with u hu using by
          simp [H, Function.update_of_ne hu]
      ·                                                     
        simpa [H, continuousAt_update_same] using riemannZeta_residue_one
    ·                                                        
      have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - 1) * riemannZeta u) z := by
        have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) z := (differentiableAt_id.sub_const 1)
        have h2 : DifferentiableAt ℂ riemannZeta z := (differentiableAt_riemannZeta hz)
        exact h1.mul h2
      apply DifferentiableAt.congr_of_eventuallyEq hdiff
      filter_upwards [eventually_ne_nhds hz] with u hu using by
        simp [H, Function.update_of_ne hu]

  let G : ℂ → ℂ := fun z => - (deriv H z) / H z

  have h_eq_on_pos : ∀ ⦃δ : ℝ⦄, 0 < δ →
      (-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))) = G ((1 : ℂ) + δ) := by
    intro δ hδ
                    
    let z : ℂ := (1 : ℂ) + δ
    have hz_ne_one : z ≠ (1 : ℂ) := by
      intro h
      have hre : (1 + δ : ℝ) = 1 := by
        simpa [z, Complex.add_re, Complex.ofReal_re] using congrArg Complex.re h
      have : δ = 0 := by linarith
      exact (ne_of_gt hδ) this
    have hzeta_ne : riemannZeta z ≠ 0 := by
      have : 1 < z.re := by simpa [z, Complex.add_re, Complex.ofReal_re] using by linarith
      exact riemannZeta_ne_zero_of_one_le_re (le_of_lt this)

    have h_id_deriv : deriv (fun u : ℂ => u - 1) z = 1 := by
      exact ((hasDerivAt_id z).sub_const 1).deriv
    have h_log_id : logDeriv (fun u : ℂ => u - 1) z = 1 / (z - 1) := by
      simp [logDeriv_apply, h_id_deriv]
    have hz1 : z - 1 ≠ 0 := by simpa using sub_ne_zero.mpr hz_ne_one
    have hζ : riemannZeta z ≠ 0 := hzeta_ne

    have h_deriv_mul : deriv (fun u : ℂ => (u - 1) * riemannZeta u) z
          = riemannZeta z + (z - 1) * deriv riemannZeta z := by
      have h1 : HasDerivAt (fun u : ℂ => u - 1) 1 z := (hasDerivAt_id z).sub_const 1
      have h2 : HasDerivAt riemannZeta (deriv riemannZeta z) z :=
        (differentiableAt_riemannZeta hz_ne_one).hasDerivAt
      simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using! (h1.mul h2).deriv

    have h_prodLog :
        logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z =
          logDeriv (fun u : ℂ => u - 1) z + logDerivZeta z := by
      have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) z := (differentiableAt_id.sub_const 1)
      have h2 : DifferentiableAt ℂ riemannZeta z := (differentiableAt_riemannZeta hz_ne_one)
      have hfnz : (fun u : ℂ => u - 1) z ≠ 0 := by simpa using hz1
      have hgnz : riemannZeta z ≠ 0 := hζ
      simpa [logDerivZeta] using!
        (logDeriv_mul (x := z) (f := fun u : ℂ => u - 1) (g := riemannZeta) hfnz hgnz h1 h2)

    have h_step : -logDerivZeta z - (1 / (z - 1))
        = - logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z := by
      have : logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z
            = 1 / (z - 1) + logDerivZeta z := by
        simpa [h_log_id, add_comm] using h_prodLog
      have hneg : - logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z
                 = - (1 / (z - 1) + logDerivZeta z) := by
        simpa using congrArg Neg.neg this
      simpa [sub_eq_add_neg, add_comm] using hneg.symm

    have h_H_eq : H z = (z - 1) * riemannZeta z := by
      simp [H, Function.update_of_ne hz_ne_one]

    have h_eq_event : (fun u : ℂ => H u) =ᶠ[nhds z] (fun u : ℂ => (u - 1) * riemannZeta u) := by
      filter_upwards [eventually_ne_nhds hz_ne_one] with u hu
      simp [H, Function.update_of_ne hu]

    have h_hasDeriv_prod :
        HasDerivAt (fun u : ℂ => (u - 1) * riemannZeta u)
          (riemannZeta z + (z - 1) * deriv riemannZeta z) z := by
      have h1 : HasDerivAt (fun u : ℂ => u - 1) 1 z := (hasDerivAt_id z).sub_const 1
      have h2 : HasDerivAt riemannZeta (deriv riemannZeta z) z :=
        (differentiableAt_riemannZeta hz_ne_one).hasDerivAt
      simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using! (h1.mul h2)

    have h_hasDeriv_H :
        HasDerivAt H (riemannZeta z + (z - 1) * deriv riemannZeta z) z :=
      h_hasDeriv_prod.congr_of_eventuallyEq h_eq_event

    have h_dH : deriv H z = riemannZeta z + (z - 1) * deriv riemannZeta z := by
      simpa using h_hasDeriv_H.deriv

    have h_log_to_G : - logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z = G z := by
      have h' : logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z = (deriv H z) / H z := by
        simp [logDeriv_apply, h_H_eq, h_dH, h_deriv_mul]
      have hneg' := congrArg (fun w => -w) h'
      simpa [G, neg_div] using hneg'

    have : -logDerivZeta z - (1 / (z - 1)) = G z := by
      simpa using h_step.trans h_log_to_G

    simpa [z] using this

  let F : ℝ → ℂ := fun δ => G ((1 : ℂ) + δ)

  have hH_analytic_univ : AnalyticOnNhd ℂ H Set.univ :=
    (Complex.analyticOnNhd_univ_iff_differentiable).2 hH_diff

  have hF_contOn : ContinuousOn F s := by
    intro δ0 hδ0
                           
    let s0 : ℂ := (1 : ℂ) + δ0
    have hδ0pos : 0 < δ0 := lt_of_lt_of_le h0 hδ0.1
    have hs0_ne_one : s0 ≠ (1 : ℂ) := by
      intro h
      have hre : (1 + δ0 : ℝ) = 1 := by
        simpa [s0, Complex.add_re, Complex.ofReal_re] using congrArg Complex.re h
      have : δ0 = 0 := by linarith
      exact (ne_of_gt hδ0pos) this
    have hs0_re_gt_one : 1 < s0.re := by
      simpa [s0, Complex.add_re, Complex.ofReal_re] using by linarith
    have hζ_ne : riemannZeta s0 ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (le_of_lt hs0_re_gt_one)
    have hHs0_eq : H s0 = (s0 - 1) * riemannZeta s0 := by
      simp [H, Function.update_of_ne hs0_ne_one]
    have hHs0_ne : H s0 ≠ 0 := by
      have hs0m1_ne : s0 - 1 ≠ 0 := sub_ne_zero.mpr hs0_ne_one
      have : (s0 - 1) * riemannZeta s0 ≠ 0 := mul_ne_zero hs0m1_ne hζ_ne
      simpa [hHs0_eq] using this
                                                                                
    have hH_an_at_s0 : AnalyticAt ℂ H s0 := hH_analytic_univ s0 (by simp)
    have hH'_an_at_s0 : AnalyticAt ℂ (fun z => deriv H z) s0 := hH_an_at_s0.deriv
    have hG_an_at_s0 : AnalyticAt ℂ (fun z => G z) s0 := by
      have h_div : AnalyticAt ℂ (fun z => (deriv H z) / H z) s0 :=
        hH'_an_at_s0.div hH_an_at_s0 (by simpa using hHs0_ne)
      have h_neg : AnalyticAt ℂ (fun z => -((deriv H z) / H z)) s0 := h_div.neg
      simpa [G, div_eq_mul_inv, mul_left_comm, mul_comm, mul_assoc] using h_neg
    have hG_cont_s0 : ContinuousAt (fun z : ℂ => G z) s0 := hG_an_at_s0.continuousAt
                                               
    let affine : ℝ → ℂ := fun δ => (1 : ℂ) + (δ : ℂ)
    have h_affine_at : ContinuousAt affine δ0 :=
      (continuousAt_const).add Complex.continuous_ofReal.continuousAt
                           
    have hy : affine δ0 = s0 := by simp [affine, s0]
    have hG_at : ContinuousAt (fun z : ℂ => G z) (affine δ0) := by simpa [hy] using hG_cont_s0
    have h_comp_at : ContinuousAt (fun δ : ℝ => G (affine δ)) δ0 := hG_at.comp h_affine_at
    simpa [F, s, affine] using h_comp_at.continuousWithinAt

  have h_eq_on_s : ∀ ⦃δ : ℝ⦄, δ ∈ s → f δ = F δ := by
    intro δ hδ
    have hδpos : 0 < δ := lt_of_lt_of_le h0 hδ.1
    simpa [f, F] using h_eq_on_pos hδpos

  have hK : IsCompact s := isCompact_Icc
  have hNorm_contOn : ContinuousOn (fun δ => ‖F δ‖) s := hF_contOn.norm
  have hBdd : BddAbove ((fun δ => ‖F δ‖) '' s) := IsCompact.bddAbove_image hK hNorm_contOn
  rcases hBdd with ⟨C, hC⟩

  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro δ hδa hδb
                                                               
  change ‖f δ‖ ≤ max C 0
  have hδmem : δ ∈ s := ⟨hδa, hδb⟩
  have himg : (fun δ => ‖F δ‖) δ ∈ (fun δ => ‖F δ‖) '' s := ⟨δ, hδmem, rfl⟩
  have hbound : ‖F δ‖ ≤ C := hC himg
  have hbound' : ‖F δ‖ ≤ max C 0 := le_trans hbound (le_max_left _ _)
                                       
  have hfδ_eq : f δ = F δ := h_eq_on_s hδmem
  calc
    ‖f δ‖ = ‖F δ‖ := by simp [hfδ_eq]
    _ ≤ max C 0 := hbound'

lemma norm_one_div_coe_real_le_one_of_one_le {δ : ℝ} (h : 1 ≤ δ) : ‖(1 : ℂ) / (δ : ℂ)‖ ≤ 1 := by
                                                
  have hδpos : 0 < δ := lt_of_lt_of_le zero_lt_one h
  calc
    ‖(1 : ℂ) / (δ : ℂ)‖ = ‖(1 : ℂ)‖ / ‖(δ : ℂ)‖ := by
      exact norm_div (1 : ℂ) (δ : ℂ)
    _ = 1 / ‖(δ : ℂ)‖ := by simp
    _ = 1 / |δ| := by simp
    _ = 1 / δ := by simp [abs_of_nonneg (le_of_lt hδpos)]
    _ ≤ 1 := by
                                                           
      simpa using (one_div_le_one_div_of_le (ha := (zero_lt_one)) (h := h))

lemma Z0bound_const :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0),
    ‖ -logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C := by
                                                 
  rcases uniform_bound_Z0_complex with ⟨δ0, hδ0pos, C0, hC0nonneg, hsmall⟩
                          
  let a : ℝ := min δ0 1
  have ha_pos : 0 < a := lt_min_iff.2 ⟨hδ0pos, zero_lt_one⟩
  have ha_le_one : a ≤ 1 := min_le_right _ _
  rcases bounded_on_compact_interval a 1 ha_pos ha_le_one with ⟨Cmid, hCmid_nonneg, hmid⟩
                                                       
  let C2 : ℝ := ∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ))
  have hC2_nonneg : 0 ≤ C2 := by
    have hnn : ∀ n, 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ)) :=
      vonMangoldt_rpow_nonneg 2
    exact tsum_nonneg_of_nonneg hnn
                                                                                
  let C : ℝ := 2 + C0 + Cmid + C2
  have hCgt1 : 1 < C := by
    have : 2 ≤ 2 + C0 + Cmid + C2 := by linarith [hC0nonneg, hCmid_nonneg, hC2_nonneg]
    linarith
  refine ⟨C, hCgt1, ?_⟩
  intro δ hδpos
  by_cases hlt : δ < δ0
  ·                                        
    have hbound : ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C0 :=
      hsmall δ hδpos hlt
             
    have hC0_le_C : C0 ≤ C := by linarith
    exact le_trans hbound hC0_le_C
  ·          
    have hge : δ0 ≤ δ := le_of_not_gt hlt
    rcases le_total δ 1 with hδle1 | hδge1
    ·                              
      have ha_le_δ : a ≤ δ := le_trans (min_le_left δ0 1) hge
      have hbound : ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ Cmid :=
        hmid δ ha_le_δ hδle1
                 
      have hCmid_le_C : Cmid ≤ C := by linarith
      exact le_trans hbound hCmid_le_C
    ·                                                     
                      
      let x : ℝ := 1 + δ
      have hx1 : 1 < x := by
        have : 0 < δ := hδpos
        have : 1 < 1 + δ := lt_add_of_pos_right 1 this
        exact this
                                                           
      have h_norm_eq_abs_real : ‖-logDerivZeta (x : ℂ)‖
            = |∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)| :=
        norm_negLogDerivZeta_real_eq_abs_tsum_vonMangoldt x hx1
                                      
      have eqArg : ((1 : ℂ) + δ) = (x : ℂ) := by simp [x]
                                             
      have h_norm_eq_abs : ‖-logDerivZeta ((1 : ℂ) + δ)‖
            = |∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)| := by
        simpa [eqArg] using h_norm_eq_abs_real
                              
      let S : ℝ := ∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)
      have hsum_nonneg : 0 ≤ S := by
        change 0 ≤ ∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)
        exact tsum_nonneg_of_nonneg (vonMangoldt_rpow_nonneg x)
                                                                      
      have h_norm_le_sum : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤ S := by
        have : ‖-logDerivZeta ((1 : ℂ) + δ)‖ = |S| := h_norm_eq_abs
        have : |S| = S := abs_of_nonneg hsum_nonneg
        exact le_of_eq (h_norm_eq_abs.trans this)
                                                                 
      have hx_ge_two : 2 ≤ x := by
                                     
        have : 1 ≤ δ := hδge1
        have : 2 ≤ 1 + δ := by linarith
        exact this
                                                   
      have h_le_2 : ∀ n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)
                          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ)) := by
        intro n
        by_cases h0 : n = 0
        · simp [h0]
        · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h0
          have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          have hrpow : (n : ℝ) ^ (-x) ≤ (n : ℝ) ^ (-(2 : ℝ)) :=
            rpow_neg_antitone hn' hx_ge_two
          have hΛ_nonneg : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
            ArithmeticFunction.vonMangoldt_nonneg
          exact mul_le_mul_of_nonneg_left hrpow hΛ_nonneg
                                   
      have h_summ_x : Summable (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) := by
        exact Rezetaseries0 x hx1
      have h_summ_2 : Summable (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ))) :=
        Rezetaseries0 2 (by norm_num)
      have hsum_le : S ≤ C2 := by
                                                
        have h_nonneg_x : ∀ n, 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) :=
          vonMangoldt_rpow_nonneg x
        exact tsum_le_of_nonneg_of_le h_summ_x h_summ_2 h_nonneg_x h_le_2
                                        
      have h_norm_le_C2 : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤ C2 :=
        le_trans h_norm_le_sum hsum_le
                                                                
      have h_one_div_le : ‖(1 : ℂ) / (δ : ℂ)‖ ≤ 1 := norm_one_div_coe_real_le_one_of_one_le hδge1
      have htriangle : ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖
                        ≤ ‖-logDerivZeta ((1 : ℂ) + δ)‖ + ‖(1 : ℂ) / (δ : ℂ)‖ :=
        norm_sub_le _ _
      have hlarge_bound : ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C2 + 1 := by
        refine le_trans htriangle ?_
        exact add_le_add h_norm_le_C2 h_one_div_le
                     
      have hC2_le_C : C2 + 1 ≤ C := by linarith
      exact le_trans hlarge_bound hC2_le_C

lemma Z0boundRe_const :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0),
    ((-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))).re) ≤ C := by
                                                 
  rcases Z0bound_const with ⟨C, hCpos, hC⟩
  use C
  constructor
  · exact hCpos
  · intro δ hδ
                                                    
    have h_bound := hC δ hδ
    exact le_trans (Complex.re_le_norm _) h_bound

lemma Z0boundRe_const2 :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0),
    ((-logDerivZeta ((1 : ℂ) + δ)).re + (-(1 / (δ : ℂ))).re) ≤ C := by
                                           
  rcases Z0boundRe_const with ⟨C, hC_pos, hC⟩
  use C, hC_pos
  intro δ hδ
  have h_sub_re : ((-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))).re) =
    ((-logDerivZeta ((1 : ℂ) + δ)).re + (-(1 / (δ : ℂ))).re) := by
    rw [Complex.sub_re]
    rfl
  rw [← h_sub_re]
  exact hC δ hδ

lemma Z0boundRe_const3 :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0),
    (-logDerivZeta ((1 : ℂ) + δ)).re - (1 / δ) ≤ C := by
                                                                        
  rcases Z0boundRe_const2 with ⟨C, hCpos, hC⟩
  use C, hCpos
  intro δ hδ
                           
  have h := hC δ hδ
                                                                  
  have h_re_eq : (-(1 / (δ : ℂ))).re = -(1 / δ) := by
    rw [Complex.neg_re, Complex.div_re, Complex.one_re, Complex.ofReal_re, Complex.ofReal_im]
    simp [Complex.normSq_ofReal]
                                          
  rwa [h_re_eq] at h

lemma Rezeta1zetaseries1 (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (-logDerivZeta ((1 : ℂ) + delta + t * I)).re = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ)) := by
                                                         
  have h1 : 1 < 1 + delta := by linarith [hdelta]
  convert (preTransparency := .instances) Rezeta1zetaseries (1 + delta) t h1
                                                
  simp [Complex.ofReal_add]

lemma Rezeta1zetaseries2 (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (-logDerivZeta ((1 : ℂ) + delta + (2 * t) * I)).re = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ)) := by
                                                             
  have h1 : 1 < 1 + delta := by linarith [hdelta]
                                                                                 
  have h2 : (1 : ℂ) + delta + (2 * t) * I = (1 + delta : ℝ) + ((2 * t) : ℝ) * I := by
    simp [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul]
  rw [h2]
  exact Rezeta1zetaseries (1 + delta) (2 * t) h1

lemma Rezeta1zetaseries0 (delta : ℝ) (hdelta : delta > 0) :
    (-logDerivZeta ((1 : ℂ) + delta)).re = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) := by
                                             
  have h_series : (-logDerivZeta ((1 : ℂ) + delta + 0 * I)).re =
                  ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (0 * Real.log (n : ℝ)) :=
    Rezeta1zetaseries1 0 delta hdelta

  have h_lhs : (-logDerivZeta ((1 : ℂ) + delta + 0 * I)).re = (-logDerivZeta ((1 : ℂ) + delta)).re := by
    congr 2
    simp

  have h_rhs : ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (0 * Real.log (n : ℝ)) =
               ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) := by
    congr 1
    funext n
    by_cases h : n = 0
    · simp [h]
    · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
      rw [lem_cost0 n hn 0 rfl, mul_one]

  rw [← h_lhs, h_series, h_rhs]

open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.Erdos970_PNT5_Strong
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970


open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real

open _root_.ArithmeticFunction (vonMangoldt)

noncomputable abbrev MellinTransform : (ℝ → ℂ) → ℂ → ℂ := mellin

noncomputable def MellinInverseTransform (F : ℂ → ℂ) (σ : ℝ) (x : ℝ) : ℂ :=
  VerticalIntegral' (fun s ↦ x ^ (-s) * F s) σ

local notation (name := mellintransform2) "𝓜" => MellinTransform

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

local notation "I" => Complex.I

noncomputable def ChebyshevPsi (x : ℝ) : ℝ :=
  (Finset.range ⌊x + 1⌋₊).sum Λ

noncomputable abbrev SmoothedChebyshevIntegrand (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ → ℂ :=
  fun s ↦ (- deriv riemannZeta s) / riemannZeta s *
    𝓜 ((Smooth1 SmoothingF ε) ·) s * (X : ℂ) ^ s

noncomputable def SmoothedChebyshev (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ :=
  VerticalIntegral' (SmoothedChebyshevIntegrand SmoothingF ε X) ((1 : ℝ) + (Real.log X)⁻¹)

open ComplexConjugate

open _root_.MeasureTheory

attribute [fun_prop] Continuous.const_cpow

noncomputable def I₁ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Iic (-T),
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

noncomputable def I₂ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - T * I)))

noncomputable def I₃₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

noncomputable def I₈ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + T * I)))

noncomputable def I₉ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Ici T,
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

noncomputable def I₃ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..(-3),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

noncomputable def I₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (3 : ℝ)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

noncomputable def I₄ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - 3 * I)))

noncomputable def I₆ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + 3 * I)))

noncomputable def I₅ (SmoothingF : ℝ → ℝ) (ε X σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-3)..3,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₂ + t * I)))

def LogDerivZetaHasBound (A C : ℝ) : Prop := ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t|)), ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤
    C * Real.log |t| ^ 9

def LogDerivZetaIsHoloSmall (σ₂ : ℝ) : Prop :=
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
    (((uIcc σ₂ 2)  ×ℂ (uIcc (-3) 3)) \ {1})

open _root_.Filter Topology

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.EulerMaclaurin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! We prove the 1st order Euler-Maclaurin formula by specialising Abel summation and manipulating integrals. -/

section

open Finset Interval MeasureTheory


variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

/-- The 1st Bernoulli function. -/
noncomputable def B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2
end
end

section
-- module Solutions.OAIQ083_JD.Jacobsthal_Sieve_SieveScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosPrimeInputs.AffinePrimeSieve

open _root_.Finset

noncomputable def value (a : ℤ) (q i : ℕ) : ℤ := a + (q:ℤ)*i

end ErdosPrimeInputs.AffinePrimeSieve

end

section

namespace ErdosPrimeInputs.SieveScale

open _root_.Filter
open scoped Topology

noncomputable def level : ℝ := 480024

end ErdosPrimeInputs.SieveScale

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ083_JD.Mathlib_Analysis_Asymptotics_Asymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Filter Topology

namespace Asymptotics

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]

variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']


theorem isLittleO_const_id_cocompact [ProperSpace F'']
    (c : E'') : (fun _x : F'' => c) =o[cocompact F''] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_norm_cocompact_atTop

-- to replace existing `isLittleO_const_id_atTop`
theorem isLittleO_const_id_atTop2 [LinearOrder F''] [NoMaxOrder F''] [ClosedIciTopology F'']
    [ProperSpace F''] (c : E'') : (fun _x : F'' => c) =o[atTop] id :=
 (isLittleO_const_id_cocompact c).mono atTop_le_cocompact

-- to replace existing `isLittleO_const_id_atBot`
theorem isLittleO_const_id_atBot2 [LinearOrder F''] [NoMinOrder F''] [ClosedIicTopology F'']
    [ProperSpace F''] (c : E'') : (fun _x : F'' => c) =o[atBot] id :=
  (isLittleO_const_id_cocompact c).mono atBot_le_cocompact

end Asymptotics
end

section
-- module Solutions.OAIQ083_JD.Mathlib_Analysis_Asymptotics_Uniformly
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Uniform Asymptotics

For a family of functions `f : ι × α → E` and `g : α → E`, we can think of
`f =O[𝓟 s ×ˢ l] fun (i, x) ↦ g x` as expressing that `f i` is O(g) uniformly on `s`.

This file provides methods for constructing `=O[𝓟 s ×ˢ l]` relations (similarly `Θ`)
and deriving their consequences.
-/

open Filter

open Topology

namespace Asymptotics

variable {α ι E F : Type*} {s : Set ι}

section Order

variable [NormedAddCommGroup α] [LinearOrder α] [ProperSpace α] [NormedAddCommGroup F]

theorem isLittleO_const_snd_atBot [NoMinOrder α] [ClosedIicTopology α] (c : F) (lx : Filter E) :
    (fun (_ : E × α) ↦ c) =o[lx ×ˢ atBot] Prod.snd := by
  refine lx.eq_or_neBot.casesOn (fun h ↦ by simp [h]) (fun _ ↦ ?_)
  change ((fun _ ↦ c) ∘ Prod.snd) =o[lx ×ˢ atBot] (id ∘ Prod.snd)
  rewrite [← isLittleO_map, map_snd_prod]
  exact isLittleO_const_id_atBot2 c

theorem isLittleO_const_snd_atTop [NoMaxOrder α] [ClosedIciTopology α] (c : F) (lx : Filter E) :
    (fun (_ : E × α) ↦ c) =o[lx ×ˢ atTop] Prod.snd := by
  refine lx.eq_or_neBot.casesOn (fun h ↦ by simp [h]) (fun _ ↦ ?_)
  change ((fun _ ↦ c) ∘ Prod.snd) =o[lx ×ˢ atTop] (id ∘ Prod.snd)
  rewrite [← isLittleO_map, map_snd_prod]
  exact isLittleO_const_id_atTop2 c

end Order

section ContinuousOn

variable [TopologicalSpace ι] {C : ι → E} {c : F}

section IsBigO

variable [SeminormedAddGroup E] [Norm F]

/-- A family of constant functions `f (i, x) = C i` is uniformly bounded w.r.t. `s` by
`⨆ i ∈ s, ‖C i‖`, if `s` is compact and `C` is continuous. -/
theorem _root_.ContinuousOn.const_isBigOWithUniformlyOn_isCompact
    (hf : ContinuousOn C s) (hs : IsCompact s) (hc : ‖c‖ ≠ 0) (l : Filter α) :
    IsBigOWith (sSup (norm '' (C '' s)) / ‖c‖) (𝓟 s ×ˢ l)
    (fun (i, _x) ↦ C i) fun _ => c := by
  refine isBigOWith_iff.mpr <| eventually_of_mem ?_ (fun x hx ↦ ?_) (U := s ×ˢ Set.univ)
  · exact prod_mem_prod (mem_principal_self s) univ_mem
  · rw [div_mul_cancel₀ _ hc]
    replace hs := hs.image_of_continuousOn hf |>.image continuous_norm
    have h_sSup := hs.isLUB_sSup <| Set.image_nonempty.mpr <| Set.image_nonempty.mpr ⟨x.1, hx.1⟩
    exact h_sSup.1 <| Set.mem_image_of_mem _ <| Set.mem_image_of_mem _ hx.1

/-- A family of constant functions `f (i, x) = C i` is uniformly O(1) w.r.t. `s`,
if `s` is compact and `C` is continuous. -/
theorem _root_.ContinuousOn.const_isBigOUniformlyOn_isCompact
    (hf : ContinuousOn C s) (hs : IsCompact s) (hc : ‖c‖ ≠ 0) (l : Filter α) :
    (fun (i, _x) ↦ C i) =O[𝓟 s ×ˢ l] fun _ => c :=
  (hf.const_isBigOWithUniformlyOn_isCompact hs hc l).isBigO

end IsBigO

section IsTheta

variable [NormedAddGroup E] [SeminormedAddGroup F]

/-- A family of constant functions `f (i, x) = C i` is uniformly bounded below w.r.t. `s` by
`⊓ i ∈ s, ‖C i‖`, if `s` is compact and `C` is continuous. -/
theorem _root_.ContinuousOn.const_isBigOWithUniformlyOn_isCompact_rev
    (hf : ContinuousOn C s) (hs : IsCompact s) (hC : ∀ i ∈ s, C i ≠ 0) (l : Filter α) :
    IsBigOWith (‖c‖ / sInf (norm '' (C '' s))) (𝓟 s ×ˢ l)
    (fun _ => c) fun (i, _x) ↦ C i := by
  refine isBigOWith_iff.mpr <| eventually_of_mem ?_ (fun x hx ↦ ?_) (U := s ×ˢ Set.univ)
  · exact prod_mem_prod (mem_principal_self s) univ_mem
  · rewrite [mul_comm_div]
    replace hs := hs.image_of_continuousOn hf |>.image continuous_norm
    have h_sInf := hs.isGLB_sInf <| Set.image_nonempty.mpr <| Set.image_nonempty.mpr ⟨x.1, hx.1⟩
    refine le_mul_of_one_le_right (norm_nonneg c) <| (one_le_div ?_).mpr <|
      h_sInf.1 <| Set.mem_image_of_mem _ <| Set.mem_image_of_mem _ hx.1
    obtain ⟨_, ⟨x, hx, hCx⟩, hnormCx⟩ := hs.sInf_mem h_sInf.nonempty
    rewrite [← hnormCx, ← hCx]
    exact (norm_ne_zero_iff.mpr (hC x hx)).symm.lt_of_le (norm_nonneg _)

/-- A family of constant functions `f (i, x) = C i` is uniformly Ω(1) w.r.t. `s`,
if `s` is compact and `C` is continuous with no zeros on `s`. -/
theorem _root_.ContinuousOn.const_isBigOUniformlyOn_isCompact_rev
    (hf : ContinuousOn C s) (hs : IsCompact s) (hC : ∀ i ∈ s, C i ≠ 0) (l : Filter α) :
    (fun _ => c) =O[𝓟 s ×ˢ l] (fun (i, _x) ↦ C i) :=
  (hf.const_isBigOWithUniformlyOn_isCompact_rev hs hC l).isBigO

/-- A family of constant functions `f (i, x) = C i` is uniformly Θ(1) w.r.t. `s`,
if `s` is compact and `C` is continuous with no zeros on `s`. -/
theorem _root_.ContinuousOn.const_isThetaUniformlyOn_isCompact (hf : ContinuousOn C s)
    (hs : IsCompact s) (hc : ‖c‖ ≠ 0) (hC : ∀ i ∈ s, C i ≠ 0) (l : Filter α) :
    (fun (i, _x) ↦ C i) =Θ[𝓟 s ×ˢ l] fun _ => c :=
  ⟨hf.const_isBigOUniformlyOn_isCompact hs hc l,
    hf.const_isBigOUniformlyOn_isCompact_rev hs hC l⟩

end IsTheta

end ContinuousOn
end Asymptotics
end

section
-- module Solutions.OAIQ083_JD.Rectangle
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}


@[simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl

@[simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm :=
  rfl
end

section
-- module Solutions.OAIQ083_JD.Sobolev
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance instCoeFunForallReal : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun

end CS
end


