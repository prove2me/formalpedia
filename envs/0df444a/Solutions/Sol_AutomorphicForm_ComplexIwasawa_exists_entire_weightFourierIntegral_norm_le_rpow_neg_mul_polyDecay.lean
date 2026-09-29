-- Prove2me | solution 1 for AutomorphicForm.ComplexIwasawa.exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/4956ba3f-5253-5741-9b96-2113ce53c59b

import Mathlib
import Theorems.Thm_AutomorphicForm_ComplexIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_ComplexIwasawa_exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay

set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open scoped ComplexConjugate RealInnerProductSpace

namespace ComplexJacquetCont

private noncomputable def PC (z : ℂ) : ℂ := ((1 + ‖z‖ ^ 2 : ℝ) : ℂ)

private noncomputable def ampC (a b : ℕ) (w : ℂ) (z : ℂ) : ℂ := z ^ a * conj z ^ b * PC z ^ (-w)

private noncomputable def kerC (ζ z : ℂ) : ℂ := Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * I))

private noncomputable def jc (a b : ℕ) (w ζ : ℂ) : ℂ := ∫ z : ℂ, ampC a b w z * kerC ζ z

private theorem one_add_sq_pos (z : ℂ) : 0 < 1 + ‖z‖ ^ 2 := by positivity

private theorem PC_ne_zero (z : ℂ) : PC z ≠ 0 := ofReal_ne_zero.mpr (one_add_sq_pos z).ne'

private theorem PC_re_pos (z : ℂ) : 0 < (PC z).re := by rw [PC, ofReal_re]; exact one_add_sq_pos z

private theorem PC_mem_slitPlane (z : ℂ) : PC z ∈ slitPlane := ofReal_mem_slitPlane.mpr (one_add_sq_pos z)

private theorem norm_PC_cpow (w z : ℂ) : ‖PC z ^ (-w)‖ = (1 + ‖z‖ ^ 2) ^ (-w.re) := by
  rw [PC, Complex.norm_cpow_eq_rpow_re_of_pos (one_add_sq_pos z), neg_re]

private theorem norm_ampC (a b : ℕ) (w z : ℂ) : ‖ampC a b w z‖ = ‖z‖ ^ (a + b) * (1 + ‖z‖ ^ 2) ^ (-w.re) := by
  rw [ampC, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, norm_PC_cpow, pow_add]

private theorem norm_kerC (ζ z : ℂ) : ‖kerC ζ z‖ = 1 := by
  rw [kerC, Complex.norm_exp]
  simp

private theorem norm_pow_le (z : ℂ) (n : ℕ) : ‖z‖ ^ n ≤ (1 + ‖z‖ ^ 2) ^ ((n : ℝ) / 2) := by
  have h : ‖z‖ ^ n = (‖z‖ ^ 2) ^ ((n : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    push_cast
    ring
  rw [h]
  exact Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)

private theorem norm_ampC_le (a b : ℕ) (w z : ℂ) :
    ‖ampC a b w z‖ ≤ (1 + ‖z‖ ^ 2) ^ (-(2 * w.re - (a + b : ℕ)) / 2) := by
  rw [norm_ampC]
  calc ‖z‖ ^ (a + b) * (1 + ‖z‖ ^ 2) ^ (-w.re)
      ≤ (1 + ‖z‖ ^ 2) ^ (((a + b : ℕ) : ℝ) / 2) * (1 + ‖z‖ ^ 2) ^ (-w.re) :=
        mul_le_mul_of_nonneg_right (norm_pow_le z (a + b)) (Real.rpow_nonneg (one_add_sq_pos z).le _)
    _ = (1 + ‖z‖ ^ 2) ^ (-(2 * w.re - (a + b : ℕ)) / 2) := by
        rw [← Real.rpow_add (one_add_sq_pos z)]
        congr 1
        ring

private theorem continuous_PC : Continuous PC := by unfold PC; fun_prop

private theorem continuous_ampC (a b : ℕ) (w : ℂ) : Continuous (ampC a b w) := by
  refine Continuous.mul ((continuous_pow a).mul ((continuous_conj.pow b))) ?_
  exact continuous_PC.cpow continuous_const fun z => PC_mem_slitPlane z

private theorem continuous_kerC (ζ : ℂ) : Continuous (kerC ζ) := by
  unfold kerC
  fun_prop

private noncomputable def thr (a b : ℕ) : ℝ := ((a + b : ℕ) : ℝ) / 2 + 1

private theorem integrable_dom (a b : ℕ) (w : ℂ) (hw : thr a b < w.re) :
    Integrable fun z : ℂ => (1 + ‖z‖ ^ 2) ^ (-(2 * w.re - (a + b : ℕ)) / 2) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 2 * w.re - (a + b : ℕ))
    (by rw [Complex.finrank_real_complex]; simp only [thr] at hw; push_cast at hw ⊢; linarith)
  exact h

private theorem integrable_ampC_mul (a b : ℕ) (w : ℂ) (hw : thr a b < w.re) (F : ℂ → ℂ) (hF : Continuous F)
    (C : ℝ) (hC : ∀ z, ‖F z‖ ≤ C) : Integrable fun z => ampC a b w z * F z := by
  refine Integrable.mono' ((integrable_dom a b w hw).mul_const (max C 0))
    ((continuous_ampC a b w).mul hF).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  rw [norm_mul]
  exact mul_le_mul (norm_ampC_le a b w z) ((hC z).trans (le_max_left _ _)) (norm_nonneg _)
    (Real.rpow_nonneg (one_add_sq_pos z).le _)

private theorem integrable_ampC_mul_kerC (a b : ℕ) (w : ℂ) (hw : thr a b < w.re) (ζ : ℂ) :
    Integrable fun z => ampC a b w z * kerC ζ z :=
  integrable_ampC_mul a b w hw (kerC ζ) (continuous_kerC ζ) 1 fun z => (norm_kerC ζ z).le

private theorem integrable_const_mul_ampC_mul_kerC (c : ℂ) (a b : ℕ) (w : ℂ) (hw : thr a b < w.re) (ζ : ℂ) :
    Integrable fun z => c * ampC a b w z * kerC ζ z := by
  have h := (integrable_ampC_mul_kerC a b w hw ζ).const_mul c
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only [mul_assoc]

end ComplexJacquetCont

namespace ComplexJacquetCont

private noncomputable def mulL (c : ℂ) : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ) c

@[scoped simp] private theorem mulL_apply (c v : ℂ) : mulL c v = c * v := rfl

private noncomputable def conjL : ℂ →L[ℝ] ℂ := (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap

@[scoped simp] private theorem conjL_apply (v : ℂ) : conjL v = conj v := rfl

private noncomputable def LP (z : ℂ) : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp ((2 : ℕ) • innerSL ℝ z)

private theorem LP_apply (z v : ℂ) : LP z v = conj z * v + z * conj v := by
  simp only [LP, ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ofRealCLM_apply, smul_eq_mul]
  rw [show (innerSL ℝ z) v = ⟪z, v⟫ from rfl, Complex.inner z v]
  have h : conj (v * conj z) = z * conj v := by rw [map_mul, Complex.conj_conj, mul_comm]
  rw [← h, mul_comm (conj z) v]
  push_cast
  rw [Complex.add_conj, mul_comm]
  push_cast
  ring

private theorem hasFDerivAt_PC (z : ℂ) : HasFDerivAt PC (LP z) z := by
  have h1 : HasFDerivAt (fun z : ℂ => 1 + ‖z‖ ^ 2) ((2 : ℕ) • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_add (1 : ℝ)
  exact Complex.ofRealCLM.hasFDerivAt.comp z h1

private theorem hasFDerivAt_pow' (a : ℕ) (z : ℂ) : HasFDerivAt (fun z : ℂ => z ^ a) (mulL (a * z ^ (a - 1))) z := by
  refine ((hasDerivAt_pow a z).hasFDerivAt.restrictScalars ℝ).congr_fderiv ?_
  ext v
  simp [mul_comm]

private theorem hasFDerivAt_conj_pow (b : ℕ) (z : ℂ) :
    HasFDerivAt (fun z : ℂ => conj z ^ b) ((mulL (b * conj z ^ (b - 1))).comp conjL) z := by
  have h1 : HasFDerivAt (fun s : ℂ => s ^ b) (mulL (b * conj z ^ (b - 1))) (conj z) := hasFDerivAt_pow' b (conj z)
  have h2 : HasFDerivAt (fun z : ℂ => conj z) conjL z := (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).hasFDerivAt
  exact h1.comp z h2

private theorem hasFDerivAt_PC_cpow (w z : ℂ) :
    HasFDerivAt (fun z : ℂ => PC z ^ (-w)) ((mulL (-w * PC z ^ (-w - 1))).comp (LP z)) z := by
  have h₂ : HasFDerivAt (fun s : ℂ => s ^ (-w)) (mulL (-w * PC z ^ (-w - 1))) (PC z) := by
    refine ((Complex.hasStrictDerivAt_cpow_const (Or.inl (PC_re_pos z))).hasDerivAt.hasFDerivAt.restrictScalars
      ℝ).congr_fderiv ?_
    ext v
    simp [mul_comm]
  exact h₂.comp z (hasFDerivAt_PC z)

private noncomputable def Lamp (a b : ℕ) (w z : ℂ) : ℂ →L[ℝ] ℂ :=
  (z ^ a * conj z ^ b) • ((mulL (-w * PC z ^ (-w - 1))).comp (LP z))
    + PC z ^ (-w) • ((z ^ a) • ((mulL (b * conj z ^ (b - 1))).comp conjL) + (conj z ^ b) • mulL (a * z ^ (a - 1)))

private theorem hasFDerivAt_ampC (a b : ℕ) (w z : ℂ) : HasFDerivAt (ampC a b w) (Lamp a b w z) z :=
  ((hasFDerivAt_pow' a z).mul (hasFDerivAt_conj_pow b z)).mul (hasFDerivAt_PC_cpow w z)

private theorem Lamp_apply (a b : ℕ) (w z v : ℂ) :
    Lamp a b w z v = a * v * ampC (a - 1) b w z + b * conj v * ampC a (b - 1) w z
      - w * v * ampC a (b + 1) (w + 1) z - w * conj v * ampC (a + 1) b (w + 1) z := by
  have hP0 := PC_ne_zero z
  have e1 : PC z ^ (-(w + 1)) = PC z ^ (-w - 1) := by rw [neg_add']
  simp only [Lamp, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, mulL_apply, conjL_apply, LP_apply, smul_eq_mul, ampC, e1, pow_succ]
  ring

private noncomputable def MC (ζ : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp ((4 * Real.pi) • (Complex.reCLM.comp (mulL ζ)))

private theorem MC_apply (ζ v : ℂ) : MC ζ v = ((4 * Real.pi * (ζ * v).re : ℝ) : ℂ) := by
  simp [MC, mul_assoc]

private noncomputable def dd (ζ : ℂ) : ℂ := ((4 * Real.pi * ‖ζ‖ ^ 2 : ℝ) : ℂ) * I

private theorem dd_ne_zero (ζ : ℂ) (hζ : ζ ≠ 0) : dd ζ ≠ 0 :=
  mul_ne_zero (ofReal_ne_zero.mpr (by positivity)) I_ne_zero

private theorem norm_dd (ζ : ℂ) : ‖dd ζ‖ = 4 * Real.pi * ‖ζ‖ ^ 2 := by
  rw [dd, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

private theorem hasFDerivAt_kerC (ζ z : ℂ) :
    ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (kerC ζ) L z ∧ ∀ v : ℂ, L v = -(MC ζ v) * I * kerC ζ z := by
  have hfun : kerC ζ = fun z => Complex.exp (-(MC ζ z) * I) := by
    funext z; rw [kerC, MC_apply, neg_mul]
  have h1 : HasFDerivAt (fun z => -(MC ζ z) * I) (I • (-(MC ζ))) z := ((MC ζ).hasFDerivAt.neg).mul_const I
  refine ⟨_, by rw [hfun]; exact h1.cexp, fun v => ?_⟩
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul]
  rw [show cexp (-(MC ζ) z * I) = kerC ζ z from (congrFun hfun z).symm]
  ring

private theorem MC_conj (ζ : ℂ) : MC ζ (conj ζ) * I = dd ζ := by
  rw [MC_apply, dd, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

end ComplexJacquetCont
p2m_reactivate "P2MW.S_AutomorphicForm_ComplexIwasawa_exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay.ComplexJacquetCont"

namespace ComplexJacquetCont

private theorem jc_halfplane (a b : ℕ) :
    ContinuousOn (fun q : ℂ × ℂ => jc a b q.1 q.2) ({w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re} ×ˢ Set.univ) ∧
    (∀ ζ : ℂ, DifferentiableOn ℂ (fun w : ℂ => jc a b w ζ) {w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re}) ∧
    (∀ K : Set ℂ, IsCompact K → K ⊆ {w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re} → ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ w ∈ K, ∀ ζ : ℂ, ‖jc a b w ζ‖ ≤ C * (1 + ‖ζ‖) ^ (-(N : ℝ))) :=
  AutomorphicForm.ComplexIwasawa.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral a b

private theorem thr_eq (a b : ℕ) : thr a b = ((a + b : ℕ) : ℝ) / 2 + 1 := rfl

private theorem thr_sub_one_le (a b : ℕ) : thr (a - 1) b ≤ thr a b := by
  simp only [thr]
  have : ((a - 1 + b : ℕ) : ℝ) ≤ ((a + b : ℕ) : ℝ) := by exact_mod_cast (by omega : a - 1 + b ≤ a + b)
  linarith

private theorem thr_sub_one_le' (a b : ℕ) : thr a (b - 1) ≤ thr a b := by
  simp only [thr]
  have : ((a + (b - 1) : ℕ) : ℝ) ≤ ((a + b : ℕ) : ℝ) := by exact_mod_cast (by omega : a + (b - 1) ≤ a + b)
  linarith

private theorem thr_add_one (a b : ℕ) : thr a (b + 1) = thr a b + 1 / 2 := by
  simp only [thr]; push_cast; ring

private theorem thr_add_one' (a b : ℕ) : thr (a + 1) b = thr a b + 1 / 2 := by
  simp only [thr]; push_cast; ring

private theorem re_add_one (w : ℂ) : (w + 1).re = w.re + 1 := by simp

private theorem jc_step (a b : ℕ) (w : ℂ) (hw : thr a b < w.re) (ζ : ℂ) (hζ : ζ ≠ 0) :
    jc a b w ζ = (dd ζ)⁻¹ * (a * conj ζ * jc (a - 1) b w ζ + b * ζ * jc a (b - 1) w ζ
      - w * conj ζ * jc a (b + 1) (w + 1) ζ - w * ζ * jc (a + 1) b (w + 1) ζ) := by

  have h1 : thr (a - 1) b < w.re := (thr_sub_one_le a b).trans_lt hw
  have h2 : thr a (b - 1) < w.re := (thr_sub_one_le' a b).trans_lt hw
  have h3 : thr a (b + 1) < (w + 1).re := by rw [thr_add_one, re_add_one]; linarith
  have h4 : thr (a + 1) b < (w + 1).re := by rw [thr_add_one', re_add_one]; linarith

  have hf : ∀ z, HasFDerivAt (ampC a b w) (Lamp a b w z) z := hasFDerivAt_ampC a b w
  choose Lg hLg hLgv using fun z => hasFDerivAt_kerC ζ z
  have hfd : ∀ z, fderiv ℝ (ampC a b w) z (conj ζ) = a * conj ζ * ampC (a - 1) b w z + b * ζ * ampC a (b - 1) w z
      - w * conj ζ * ampC a (b + 1) (w + 1) z - w * ζ * ampC (a + 1) b (w + 1) z := by
    intro z
    rw [(hf z).fderiv, Lamp_apply, Complex.conj_conj]
  have hgd : ∀ z, fderiv ℝ (kerC ζ) z (conj ζ) = -dd ζ * kerC ζ z := by
    intro z
    rw [(hLg z).fderiv, hLgv, ← MC_conj]
    ring

  have hfg : Integrable fun z => ampC a b w z * kerC ζ z := integrable_ampC_mul_kerC a b w hw ζ
  have hfg' : Integrable fun z => ampC a b w z * fderiv ℝ (kerC ζ) z (conj ζ) := by
    simp_rw [hgd]
    exact integrable_ampC_mul a b w hw _ (continuous_const.mul (continuous_kerC ζ)) ‖dd ζ‖
      fun z => by rw [norm_mul, norm_neg, norm_kerC, mul_one]
  have hI1 := integrable_const_mul_ampC_mul_kerC (a * conj ζ) (a - 1) b w h1 ζ
  have hI2 := integrable_const_mul_ampC_mul_kerC (b * ζ) a (b - 1) w h2 ζ
  have hI3 := integrable_const_mul_ampC_mul_kerC (w * conj ζ) a (b + 1) (w + 1) h3 ζ
  have hI4 := integrable_const_mul_ampC_mul_kerC (w * ζ) (a + 1) b (w + 1) h4 ζ
  have hf'g_eq : (fun z => fderiv ℝ (ampC a b w) z (conj ζ) * kerC ζ z)
      = fun z => a * conj ζ * ampC (a - 1) b w z * kerC ζ z + b * ζ * ampC a (b - 1) w z * kerC ζ z
        - w * conj ζ * ampC a (b + 1) (w + 1) z * kerC ζ z - w * ζ * ampC (a + 1) b (w + 1) z * kerC ζ z := by
    funext z
    rw [hfd]
    ring
  have hf'g : Integrable fun z => fderiv ℝ (ampC a b w) z (conj ζ) * kerC ζ z := by
    rw [hf'g_eq]
    exact ((hI1.add hI2).sub' hI3).sub' hI4

  have hparts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure ℂ)) hf'g hfg' hfg
    (fun z _ => (hf z).differentiableAt) (fun z _ => (hLg z).differentiableAt)

  have hL : ∫ z, ampC a b w z * fderiv ℝ (kerC ζ) z (conj ζ) = -dd ζ * jc a b w ζ := by
    rw [jc, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hgd]
    ring

  have hR : ∫ z, fderiv ℝ (ampC a b w) z (conj ζ) * kerC ζ z
      = a * conj ζ * jc (a - 1) b w ζ + b * ζ * jc a (b - 1) w ζ
        - w * conj ζ * jc a (b + 1) (w + 1) ζ - w * ζ * jc (a + 1) b (w + 1) ζ := by
    rw [hf'g_eq, integral_sub, integral_sub, integral_add]
    · simp only [jc, ← integral_const_mul, mul_assoc]
    · exact hI1
    · exact hI2
    · exact hI1.add hI2
    · exact hI3
    · exact (hI1.add hI2).sub' hI3
    · exact hI4
  rw [hL, hR] at hparts
  rw [eq_inv_mul_iff_mul_eq₀ (dd_ne_zero ζ hζ)]
  linear_combination -hparts

end ComplexJacquetCont
p2m_reactivate "P2MW.S_AutomorphicForm_ComplexIwasawa_exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay.ComplexJacquetCont"

namespace ComplexJacquetCont

private noncomputable def TC (G : ℕ → ℕ → ℂ → ℂ → ℂ) : ℕ → ℕ → ℂ → ℂ → ℂ := fun a b w ζ =>
  (dd ζ)⁻¹ * (a * conj ζ * G (a - 1) b w ζ + b * ζ * G a (b - 1) w ζ
    - w * conj ζ * G a (b + 1) (w + 1) ζ - w * ζ * G (a + 1) b (w + 1) ζ)

private noncomputable def iterC (M : ℕ) : ℕ → ℕ → ℂ → ℂ → ℂ := (TC^[M]) jc

private theorem iterC_zero : iterC 0 = jc := rfl

private theorem iterC_succ (M : ℕ) : iterC (M + 1) = TC (iterC M) := Function.iterate_succ_apply' TC M jc

private theorem iterC_succ' (M : ℕ) : iterC (M + 1) = (TC^[M]) (TC jc) := Function.iterate_succ_apply TC M jc

private theorem thr_pred {a : ℕ} (ha : 0 < a) (b : ℕ) : thr (a - 1) b = thr a b - 1 / 2 := by
  simp only [thr]
  have : ((a - 1 + b : ℕ) : ℝ) = ((a + b : ℕ) : ℝ) - 1 := by
    rw [show a - 1 + b = a + b - 1 by omega, Nat.cast_sub (by omega)]; simp
  rw [this]; ring

private theorem thr_pred' (a : ℕ) {b : ℕ} (hb : 0 < b) : thr a (b - 1) = thr a b - 1 / 2 := by
  simp only [thr]
  have : ((a + (b - 1) : ℕ) : ℝ) = ((a + b : ℕ) : ℝ) - 1 := by
    rw [show a + (b - 1) = a + b - 1 by omega, Nat.cast_sub (by omega)]; simp
  rw [this]; ring

private theorem TC_jc (a b : ℕ) (w ζ : ℂ) (hw : thr a b < w.re) (hζ : ζ ≠ 0) : TC jc a b w ζ = jc a b w ζ :=
  (jc_step a b w hw ζ hζ).symm

private theorem TC_congr {G G' : ℕ → ℕ → ℂ → ℂ → ℂ} {D : ℝ}
    (h : ∀ (a b : ℕ) (w ζ : ℂ), thr a b - D < w.re → ζ ≠ 0 → G a b w ζ = G' a b w ζ)
    (a b : ℕ) (w ζ : ℂ) (hw : thr a b - D - 1 / 2 < w.re) (hζ : ζ ≠ 0) : TC G a b w ζ = TC G' a b w ζ := by
  have hA : (a : ℂ) * conj ζ * G (a - 1) b w ζ = (a : ℂ) * conj ζ * G' (a - 1) b w ζ := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · rw [h (a - 1) b w ζ (by rw [thr_pred ha]; linarith) hζ]
  have hB : (b : ℂ) * ζ * G a (b - 1) w ζ = (b : ℂ) * ζ * G' a (b - 1) w ζ := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · rw [h a (b - 1) w ζ (by rw [thr_pred' a hb]; linarith) hζ]
  have hC : G a (b + 1) (w + 1) ζ = G' a (b + 1) (w + 1) ζ :=
    h a (b + 1) (w + 1) ζ (by rw [thr_add_one, re_add_one]; linarith) hζ
  have hD : G (a + 1) b (w + 1) ζ = G' (a + 1) b (w + 1) ζ :=
    h (a + 1) b (w + 1) ζ (by rw [thr_add_one', re_add_one]; linarith) hζ
  simp only [TC, hA, hB, hC, hD]

private theorem iterate_TC_congr (M : ℕ) : ∀ {G G' : ℕ → ℕ → ℂ → ℂ → ℂ} {D : ℝ},
    (∀ (a b : ℕ) (w ζ : ℂ), thr a b - D < w.re → ζ ≠ 0 → G a b w ζ = G' a b w ζ) →
    ∀ (a b : ℕ) (w ζ : ℂ), thr a b - D - M / 2 < w.re → ζ ≠ 0 → (TC^[M]) G a b w ζ = (TC^[M]) G' a b w ζ := by
  induction M with
  | zero => intro G G' D h a b w ζ hw hζ; exact h a b w ζ (by simpa using hw) hζ
  | succ M ih =>
    intro G G' D h a b w ζ hw hζ
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine TC_congr (D := D + M / 2) (fun a b w ζ hw hζ => ih h a b w ζ (by linarith) hζ) a b w ζ ?_ hζ
    push_cast at hw ⊢
    linarith

private theorem iterC_eq_jc (M : ℕ) : ∀ (a b : ℕ) (w ζ : ℂ), thr a b < w.re → ζ ≠ 0 → iterC M a b w ζ = jc a b w ζ := by
  induction M with
  | zero => intro a b w ζ _ _; rfl
  | succ M ih =>
    intro a b w ζ hw hζ
    rw [iterC_succ, TC_congr (D := 0) (fun a b w ζ hw hζ => ih a b w ζ (by linarith) hζ) a b w ζ (by linarith) hζ]
    exact TC_jc a b w ζ hw hζ

private theorem iterC_succ_eq (M : ℕ) (a b : ℕ) (w ζ : ℂ) (hw : thr a b - M / 2 < w.re) (hζ : ζ ≠ 0) :
    iterC (M + 1) a b w ζ = iterC M a b w ζ := by
  rw [iterC_succ', iterC]
  exact iterate_TC_congr M (D := 0) (fun a b w ζ hw hζ => TC_jc a b w ζ (by linarith) hζ) a b w ζ
    (by linarith) hζ

private theorem iterC_eq_iterC_of_le {M M' : ℕ} (hMM : M ≤ M') (a b : ℕ) (w ζ : ℂ) (hw : thr a b - M / 2 < w.re)
    (hζ : ζ ≠ 0) : iterC M' a b w ζ = iterC M a b w ζ := by
  induction M', hMM using Nat.le_induction with
  | base => rfl
  | succ M' hMM' ih =>
    rw [← ih]
    refine iterC_succ_eq M' a b w ζ ?_ hζ
    have : (M : ℝ) ≤ M' := by exact_mod_cast hMM'
    linarith

private noncomputable def MofC (a b : ℕ) (w : ℂ) : ℕ := ⌈2 * (thr a b - w.re)⌉₊ + 1

private theorem MofC_spec (a b : ℕ) (w : ℂ) : thr a b - (MofC a b w : ℝ) / 2 < w.re := by
  have h := Nat.le_ceil (2 * (thr a b - w.re))
  simp only [MofC]
  push_cast
  linarith

private noncomputable def JC (a b : ℕ) (w ζ : ℂ) : ℂ := iterC (MofC a b w) a b w ζ

private theorem JC_eq_iterC (a b : ℕ) (M : ℕ) (w ζ : ℂ) (hw : thr a b - M / 2 < w.re) (hζ : ζ ≠ 0) :
    JC a b w ζ = iterC M a b w ζ := by
  unfold JC
  rcases le_total M (MofC a b w) with h | h
  · exact iterC_eq_iterC_of_le h a b w ζ hw hζ
  · exact (iterC_eq_iterC_of_le h a b w ζ (MofC_spec a b w) hζ).symm

private theorem isOpen_re_gt (c : ℝ) : IsOpen {w : ℂ | c < w.re} := isOpen_lt continuous_const Complex.continuous_re

private theorem region_zero (a b : ℕ) : {w : ℂ | thr a b - ((0 : ℕ) : ℝ) / 2 < w.re} = {w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re} := by
  ext w; simp [thr]

private theorem region_succ (a b : ℕ) (M : ℕ) :
    {w : ℂ | thr a b - ((M + 1 : ℕ) : ℝ) / 2 < w.re} = {w : ℂ | thr a b - (M : ℝ) / 2 - 1 / 2 < w.re} := by
  ext w
  simp only [mem_setOf_eq]
  push_cast
  constructor <;> intro h <;> linarith

private theorem TC_differentiableOn {G : ℕ → ℕ → ℂ → ℂ → ℂ} {D : ℝ}
    (h : ∀ (a b : ℕ) (ζ : ℂ), ζ ≠ 0 → DifferentiableOn ℂ (fun w => G a b w ζ) {w : ℂ | thr a b - D < w.re})
    (a b : ℕ) (ζ : ℂ) (hζ : ζ ≠ 0) :
    DifferentiableOn ℂ (fun w => TC G a b w ζ) {w : ℂ | thr a b - D - 1 / 2 < w.re} := by
  have hA : DifferentiableOn ℂ (fun w => (a : ℂ) * conj ζ * G (a - 1) b w ζ) {w : ℂ | thr a b - D - 1 / 2 < w.re} := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · exact (differentiableOn_const 0).congr fun w _ => by simp
    · refine ((h (a - 1) b ζ hζ).mono fun w hw => ?_).const_mul _
      simp only [mem_setOf_eq, thr_pred ha] at hw ⊢; linarith
  have hB : DifferentiableOn ℂ (fun w => (b : ℂ) * ζ * G a (b - 1) w ζ) {w : ℂ | thr a b - D - 1 / 2 < w.re} := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · exact (differentiableOn_const 0).congr fun w _ => by simp
    · refine ((h a (b - 1) ζ hζ).mono fun w hw => ?_).const_mul _
      simp only [mem_setOf_eq, thr_pred' a hb] at hw ⊢; linarith
  have hC : DifferentiableOn ℂ (fun w => G a (b + 1) (w + 1) ζ) {w : ℂ | thr a b - D - 1 / 2 < w.re} :=
    (h a (b + 1) ζ hζ).comp (differentiable_id.add_const 1).differentiableOn fun w hw => by
      simp only [mem_setOf_eq, re_add_one, thr_add_one] at hw ⊢; linarith
  have hD : DifferentiableOn ℂ (fun w => G (a + 1) b (w + 1) ζ) {w : ℂ | thr a b - D - 1 / 2 < w.re} :=
    (h (a + 1) b ζ hζ).comp (differentiable_id.add_const 1).differentiableOn fun w hw => by
      simp only [mem_setOf_eq, re_add_one, thr_add_one'] at hw ⊢; linarith
  simp only [TC]
  exact (((hA.add hB).sub ((differentiableOn_id.mul (differentiableOn_const _)).mul hC)).sub
    ((differentiableOn_id.mul (differentiableOn_const _)).mul hD)).const_mul _

private theorem iterC_differentiableOn (M : ℕ) : ∀ (a b : ℕ) (ζ : ℂ), ζ ≠ 0 →
    DifferentiableOn ℂ (fun w => iterC M a b w ζ) {w : ℂ | thr a b - (M : ℝ) / 2 < w.re} := by
  induction M with
  | zero => intro a b ζ _; rw [region_zero]; simpa [iterC_zero] using (jc_halfplane a b).2.1 ζ
  | succ M ih =>
    intro a b ζ hζ
    rw [iterC_succ, region_succ]
    exact TC_differentiableOn (D := M / 2) ih a b ζ hζ

private theorem differentiable_JC (a b : ℕ) (ζ : ℂ) (hζ : ζ ≠ 0) : Differentiable ℂ (fun w => JC a b w ζ) := by
  intro w₀
  set M := MofC a b w₀
  have hU : {w : ℂ | thr a b - (M : ℝ) / 2 < w.re} ∈ 𝓝 w₀ := (isOpen_re_gt _).mem_nhds (MofC_spec a b w₀)
  have hd : DifferentiableAt ℂ (fun w => iterC M a b w ζ) w₀ := (iterC_differentiableOn M a b ζ hζ).differentiableAt hU
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hU] with w hw
  exact JC_eq_iterC a b M w ζ hw hζ

private theorem JC_eq_jc (a b : ℕ) (w ζ : ℂ) (hw : thr a b < w.re) (hζ : ζ ≠ 0) : JC a b w ζ = jc a b w ζ := by
  unfold JC
  exact iterC_eq_jc _ a b w ζ hw hζ

private theorem continuous_dd : Continuous dd := by
  unfold dd; fun_prop

private theorem TC_continuousOn {G : ℕ → ℕ → ℂ → ℂ → ℂ} {D : ℝ}
    (h : ∀ a b : ℕ, ContinuousOn (fun p : ℂ × ℂ => G a b p.1 p.2) ({w : ℂ | thr a b - D < w.re} ×ˢ {ζ : ℂ | ζ ≠ 0}))
    (a b : ℕ) :
    ContinuousOn (fun p : ℂ × ℂ => TC G a b p.1 p.2) ({w : ℂ | thr a b - D - 1 / 2 < w.re} ×ˢ {ζ : ℂ | ζ ≠ 0}) := by
  set S : Set (ℂ × ℂ) := {w : ℂ | thr a b - D - 1 / 2 < w.re} ×ˢ {ζ : ℂ | ζ ≠ 0} with hS
  have hdd : ContinuousOn (fun p : ℂ × ℂ => (dd p.2)⁻¹) S :=
    (continuous_dd.comp continuous_snd).continuousOn.inv₀ fun p hp => dd_ne_zero p.2 hp.2
  have hconj : Continuous fun p : ℂ × ℂ => conj p.2 := continuous_conj.comp continuous_snd
  have hA : ContinuousOn (fun p : ℂ × ℂ => (a : ℂ) * conj p.2 * G (a - 1) b p.1 p.2) S := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · exact (continuousOn_const (c := (0 : ℂ))).congr fun p _ => by simp
    · refine (continuousOn_const.mul hconj.continuousOn).mul ((h (a - 1) b).mono fun p hp => ?_)
      simp only [hS, mem_prod, mem_setOf_eq, thr_pred ha] at hp ⊢
      exact ⟨by linarith [hp.1], hp.2⟩
  have hB : ContinuousOn (fun p : ℂ × ℂ => (b : ℂ) * p.2 * G a (b - 1) p.1 p.2) S := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · exact (continuousOn_const (c := (0 : ℂ))).congr fun p _ => by simp
    · refine (continuousOn_const.mul continuous_snd.continuousOn).mul ((h a (b - 1)).mono fun p hp => ?_)
      simp only [hS, mem_prod, mem_setOf_eq, thr_pred' a hb] at hp ⊢
      exact ⟨by linarith [hp.1], hp.2⟩
  have hshift : ∀ a' b', thr a' b' = thr a b + 1 / 2 →
      ContinuousOn (fun p : ℂ × ℂ => G a' b' (p.1 + 1) p.2) S := by
    intro a' b' hab
    refine (h a' b').comp ((continuous_fst.add continuous_const).prodMk continuous_snd).continuousOn fun p hp => ?_
    simp only [hS, mem_prod, mem_setOf_eq, Pi.add_apply, re_add_one, hab] at hp ⊢
    exact ⟨by linarith [hp.1], hp.2⟩
  have hC := hshift a (b + 1) (thr_add_one a b)
  have hD := hshift (a + 1) b (thr_add_one' a b)
  simp only [TC]
  exact hdd.mul (((hA.add hB).sub ((continuous_fst.continuousOn.mul hconj.continuousOn).mul hC)).sub
    ((continuous_fst.continuousOn.mul continuous_snd.continuousOn).mul hD))

private theorem iterC_continuousOn (M : ℕ) : ∀ a b : ℕ,
    ContinuousOn (fun p : ℂ × ℂ => iterC M a b p.1 p.2) ({w : ℂ | thr a b - (M : ℝ) / 2 < w.re} ×ˢ {ζ : ℂ | ζ ≠ 0}) := by
  induction M with
  | zero =>
    intro a b
    rw [region_zero]
    exact (jc_halfplane a b).1.mono (prod_mono le_rfl (subset_univ _))
  | succ M ih =>
    intro a b
    rw [iterC_succ, region_succ]
    exact TC_continuousOn (D := M / 2) ih a b

private theorem continuousOn_JC (a b : ℕ) :
    ContinuousOn (fun p : ℂ × ℂ => JC a b p.1 p.2) (Set.univ ×ˢ {ζ : ℂ | ζ ≠ 0}) := by
  intro p hp
  obtain ⟨w₀, ζ₀⟩ := p
  have hζ₀ : ζ₀ ≠ 0 := hp.2
  set M := MofC a b w₀
  have hV : ({w : ℂ | thr a b - (M : ℝ) / 2 < w.re} ×ˢ {ζ : ℂ | ζ ≠ 0}) ∈ 𝓝 (w₀, ζ₀) :=
    ((isOpen_re_gt _).prod isOpen_ne).mem_nhds ⟨MofC_spec a b w₀, hζ₀⟩
  have hc : ContinuousAt (fun p : ℂ × ℂ => iterC M a b p.1 p.2) (w₀, ζ₀) := (iterC_continuousOn M a b).continuousAt hV
  refine (hc.congr_of_eventuallyEq ?_).continuousWithinAt
  filter_upwards [hV] with p hp'
  exact JC_eq_iterC a b M p.1 p.2 hp'.1 hp'.2

end ComplexJacquetCont
p2m_reactivate "P2MW.S_AutomorphicForm_ComplexIwasawa_exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay.ComplexJacquetCont"

namespace ComplexJacquetCont

private def BoundOnC (G : ℕ → ℕ → ℂ → ℂ → ℂ) (D : ℝ) (m : ℕ) : Prop :=
  ∀ (a b : ℕ) (K : Set ℂ), IsCompact K → K ⊆ {w : ℂ | thr a b - D < w.re} → ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ w ∈ K, ∀ ζ : ℂ, ζ ≠ 0 → ‖G a b w ζ‖ ≤ C * ‖ζ‖ ^ (-(m : ℝ)) * (1 + ‖ζ‖) ^ (-(N : ℝ))

private theorem norm_dd_inv_mul_norm (ζ : ℂ) (hζ : ζ ≠ 0) : ‖(dd ζ)⁻¹‖ * ‖ζ‖ = (4 * Real.pi)⁻¹ * ‖ζ‖ ^ (-(1 : ℝ)) := by
  have h0 : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  rw [norm_inv, norm_dd, Real.rpow_neg_one]
  field_simp

private theorem TC_boundOn {G : ℕ → ℕ → ℂ → ℂ → ℂ} {D : ℝ} {m : ℕ} (h : BoundOnC G D m) :
    BoundOnC (TC G) (D + 1 / 2) (m + 1) := by
  intro a b K hK hKsub N
  have hKsub' : ∀ w ∈ K, thr a b - D - 1 / 2 < w.re := fun w hw => by have := hKsub hw; simp at this; linarith

  have hK1 : IsCompact ((fun w : ℂ => w + 1) '' K) := hK.image (continuous_id.add continuous_const)
  have hK1sub : ∀ a' b', thr a' b' = thr a b + 1 / 2 → (fun w : ℂ => w + 1) '' K ⊆ {w : ℂ | thr a' b' - D < w.re} := by
    rintro a' b' hab _ ⟨w, hw, rfl⟩
    have := hKsub' w hw
    simp only [mem_setOf_eq, re_add_one, hab]
    linarith
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn continuousOn_id

  set X : ℂ → ℝ := fun ζ => ‖ζ‖ ^ (-(m : ℝ)) * (1 + ‖ζ‖) ^ (-(N : ℝ)) with hX
  have hX0 : ∀ ζ, 0 ≤ X ζ := fun ζ => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (by positivity) _)

  obtain ⟨B₁, hB₁0, hB₁⟩ : ∃ B₁ : ℝ, 0 ≤ B₁ ∧ ∀ w ∈ K, ∀ ζ : ℂ, ζ ≠ 0 →
      ‖(a : ℂ) * conj ζ * G (a - 1) b w ζ‖ ≤ B₁ * ‖ζ‖ * X ζ := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · exact ⟨0, le_rfl, fun w _ ζ _ => by simp⟩
    · have hsub : K ⊆ {w : ℂ | thr (a - 1) b - D < w.re} := fun w hw => by
        have := hKsub' w hw; simp only [mem_setOf_eq, thr_pred ha]; linarith
      obtain ⟨C₁, hC₁, h₁⟩ := h (a - 1) b K hK hsub N
      refine ⟨a * C₁, by positivity, fun w hw ζ hζ => ?_⟩
      rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_conj]
      calc (a : ℝ) * ‖ζ‖ * ‖G (a - 1) b w ζ‖ ≤ (a : ℝ) * ‖ζ‖ * (C₁ * X ζ) :=
            mul_le_mul_of_nonneg_left (by rw [hX, ← mul_assoc]; exact h₁ w hw ζ hζ) (by positivity)
        _ = a * C₁ * ‖ζ‖ * X ζ := by ring

  obtain ⟨B₂, hB₂0, hB₂⟩ : ∃ B₂ : ℝ, 0 ≤ B₂ ∧ ∀ w ∈ K, ∀ ζ : ℂ, ζ ≠ 0 →
      ‖(b : ℂ) * ζ * G a (b - 1) w ζ‖ ≤ B₂ * ‖ζ‖ * X ζ := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · exact ⟨0, le_rfl, fun w _ ζ _ => by simp⟩
    · have hsub : K ⊆ {w : ℂ | thr a (b - 1) - D < w.re} := fun w hw => by
        have := hKsub' w hw; simp only [mem_setOf_eq, thr_pred' a hb]; linarith
      obtain ⟨C₂, hC₂, h₂⟩ := h a (b - 1) K hK hsub N
      refine ⟨b * C₂, by positivity, fun w hw ζ hζ => ?_⟩
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      calc (b : ℝ) * ‖ζ‖ * ‖G a (b - 1) w ζ‖ ≤ (b : ℝ) * ‖ζ‖ * (C₂ * X ζ) :=
            mul_le_mul_of_nonneg_left (by rw [hX, ← mul_assoc]; exact h₂ w hw ζ hζ) (by positivity)
        _ = b * C₂ * ‖ζ‖ * X ζ := by ring

  obtain ⟨C₃, hC₃, h₃⟩ := h a (b + 1) _ hK1 (hK1sub a (b + 1) (thr_add_one a b)) N
  obtain ⟨C₄, hC₄, h₄⟩ := h (a + 1) b _ hK1 (hK1sub (a + 1) b (thr_add_one' a b)) N
  have hw' : ∀ w ∈ K, ‖w‖ ≤ |R| := fun w hw => (hR w hw).trans (le_abs_self R)
  have hB₃ : ∀ w ∈ K, ∀ ζ : ℂ, ζ ≠ 0 → ‖w * conj ζ * G a (b + 1) (w + 1) ζ‖ ≤ |R| * C₃ * ‖ζ‖ * X ζ := by
    intro w hw ζ hζ
    rw [norm_mul, norm_mul, Complex.norm_conj]
    calc ‖w‖ * ‖ζ‖ * ‖G a (b + 1) (w + 1) ζ‖ ≤ |R| * ‖ζ‖ * (C₃ * X ζ) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hw' w hw) (norm_nonneg _))
            (by rw [hX, ← mul_assoc]; exact h₃ _ ⟨w, hw, rfl⟩ ζ hζ) (norm_nonneg _) (by positivity)
      _ = |R| * C₃ * ‖ζ‖ * X ζ := by ring
  have hB₄ : ∀ w ∈ K, ∀ ζ : ℂ, ζ ≠ 0 → ‖w * ζ * G (a + 1) b (w + 1) ζ‖ ≤ |R| * C₄ * ‖ζ‖ * X ζ := by
    intro w hw ζ hζ
    rw [norm_mul, norm_mul]
    calc ‖w‖ * ‖ζ‖ * ‖G (a + 1) b (w + 1) ζ‖ ≤ |R| * ‖ζ‖ * (C₄ * X ζ) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hw' w hw) (norm_nonneg _))
            (by rw [hX, ← mul_assoc]; exact h₄ _ ⟨w, hw, rfl⟩ ζ hζ) (norm_nonneg _) (by positivity)
      _ = |R| * C₄ * ‖ζ‖ * X ζ := by ring

  set C : ℝ := (4 * Real.pi)⁻¹ * (B₁ + B₂ + |R| * C₃ + |R| * C₄ + C₃) with hCdef
  have hpi : 0 < (4 * Real.pi)⁻¹ := by positivity
  refine ⟨C, by positivity, fun w hw ζ hζ => ?_⟩
  have hζ0 : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  have hsum : ‖(a : ℂ) * conj ζ * G (a - 1) b w ζ + b * ζ * G a (b - 1) w ζ
      - w * conj ζ * G a (b + 1) (w + 1) ζ - w * ζ * G (a + 1) b (w + 1) ζ‖
      ≤ (B₁ + B₂ + |R| * C₃ + |R| * C₄ + C₃) * ‖ζ‖ * X ζ := by
    have e := norm_sub_le ((a : ℂ) * conj ζ * G (a - 1) b w ζ + b * ζ * G a (b - 1) w ζ
      - w * conj ζ * G a (b + 1) (w + 1) ζ) (w * ζ * G (a + 1) b (w + 1) ζ)
    have e' := norm_sub_le ((a : ℂ) * conj ζ * G (a - 1) b w ζ + b * ζ * G a (b - 1) w ζ)
      (w * conj ζ * G a (b + 1) (w + 1) ζ)
    have e'' := norm_add_le ((a : ℂ) * conj ζ * G (a - 1) b w ζ) (b * ζ * G a (b - 1) w ζ)
    have hextra : 0 ≤ C₃ * ‖ζ‖ * X ζ := by positivity
    nlinarith [hB₁ w hw ζ hζ, hB₂ w hw ζ hζ, hB₃ w hw ζ hζ, hB₄ w hw ζ hζ, e, e', e'', hextra]
  simp only [TC]
  rw [norm_mul]
  have hexp : (-(1 : ℝ)) + (-(m : ℝ)) = -((m + 1 : ℕ) : ℝ) := by push_cast; ring
  have hpow : ‖ζ‖ ^ (-(1 : ℝ)) * X ζ = ‖ζ‖ ^ (-((m + 1 : ℕ) : ℝ)) * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
    rw [hX, ← mul_assoc, ← Real.rpow_add hζ0, hexp]
  calc ‖(dd ζ)⁻¹‖ * ‖(a : ℂ) * conj ζ * G (a - 1) b w ζ + b * ζ * G a (b - 1) w ζ
        - w * conj ζ * G a (b + 1) (w + 1) ζ - w * ζ * G (a + 1) b (w + 1) ζ‖
      ≤ ‖(dd ζ)⁻¹‖ * ((B₁ + B₂ + |R| * C₃ + |R| * C₄ + C₃) * ‖ζ‖ * X ζ) :=
        mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = (‖(dd ζ)⁻¹‖ * ‖ζ‖) * (B₁ + B₂ + |R| * C₃ + |R| * C₄ + C₃) * X ζ := by ring
    _ = C * (‖ζ‖ ^ (-(1 : ℝ)) * X ζ) := by rw [norm_dd_inv_mul_norm ζ hζ, hCdef]; ring
    _ = C * ‖ζ‖ ^ (-((m + 1 : ℕ) : ℝ)) * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by rw [hpow, hCdef]; ring

private theorem jc_boundOn : BoundOnC jc 0 0 := by
  intro a b K hK hKsub N
  obtain ⟨C, hC, h⟩ := (jc_halfplane a b).2.2 K hK (by simpa [thr] using hKsub) N
  refine ⟨C, hC, fun w hw ζ _ => ?_⟩
  rw [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one]
  exact h w hw ζ

private theorem iterC_boundOn (M : ℕ) : BoundOnC (iterC M) (M / 2) M := by
  induction M with
  | zero => simpa [iterC_zero] using jc_boundOn
  | succ M ih =>
    have hc : ((M + 1 : ℕ) : ℝ) / 2 = (M : ℝ) / 2 + 1 / 2 := by push_cast; ring
    rw [iterC_succ, hc]
    exact TC_boundOn ih

private theorem JC_bound (a b : ℕ) (K : Set ℂ) (hK : IsCompact K) : ∃ M : ℕ, ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ w ∈ K, ∀ ζ : ℂ, ζ ≠ 0 → ‖JC a b w ζ‖ ≤ C * ‖ζ‖ ^ (-(M : ℝ)) * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn continuousOn_id
  set M : ℕ := ⌈2 * (thr a b + |R|)⌉₊ + 1 with hM
  have hKsub : K ⊆ {w : ℂ | thr a b - (M : ℝ) / 2 < w.re} := by
    intro w hw
    have h1 : ‖w‖ ≤ |R| := (hR w hw).trans (le_abs_self R)
    have h2 : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
    have h3 : -|R| ≤ w.re := by linarith [neg_abs_le w.re]
    have h4 := Nat.le_ceil (2 * (thr a b + |R|))
    have h5 : 0 ≤ thr a b + |R| := by simp only [thr]; positivity
    simp only [mem_setOf_eq, hM]
    push_cast
    linarith
  refine ⟨M, fun N => ?_⟩
  obtain ⟨C, hC, h⟩ := iterC_boundOn M a b K hK hKsub N
  refine ⟨C, hC, fun w hw ζ hζ => ?_⟩
  rw [JC_eq_iterC a b M w ζ (hKsub hw) hζ]
  exact h w hw ζ hζ

end ComplexJacquetCont
p2m_reactivate "P2MW.S_AutomorphicForm_ComplexIwasawa_exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay.ComplexJacquetCont"

open ComplexJacquetCont in
theorem solution (a b : ℕ) :
    let j : ℂ → ℂ → ℂ := fun w ζ => ∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))
    ∃ J : ℂ → ℂ → ℂ,
      (∀ ζ : ℂ, ζ ≠ 0 → Differentiable ℂ (fun w : ℂ => J w ζ)) ∧
      (∀ (w : ℂ) (ζ : ℂ), ((a + b : ℕ) : ℝ) / 2 + 1 < w.re → ζ ≠ 0 → J w ζ = j w ζ) ∧
      ContinuousOn (fun p : ℂ × ℂ => J p.1 p.2) (Set.univ ×ˢ {ζ : ℂ | ζ ≠ 0}) ∧
      (∀ K : Set ℂ, IsCompact K → ∃ M : ℕ, ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ w ∈ K, ∀ ζ : ℂ, ζ ≠ 0 → ‖J w ζ‖ ≤ C * ‖ζ‖ ^ (-(M : ℝ)) * (1 + ‖ζ‖) ^ (-(N : ℝ))) := by
  intro j
  refine ⟨JC a b, fun ζ hζ => differentiable_JC a b ζ hζ, fun w ζ hw hζ => ?_, continuousOn_JC a b, JC_bound a b⟩
  rw [JC_eq_jc a b w ζ hw hζ]
  rfl

end S_AutomorphicForm_ComplexIwasawa_exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay
end P2MW
export P2MW.S_AutomorphicForm_ComplexIwasawa_exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay (solution)
