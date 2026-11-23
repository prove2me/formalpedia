-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DifferentiableAtDerivAtZero
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DifferentiableAtDerivAtZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:38.070907+00:00
-- url     : https://prove2.me/theorems/9fc747e4-0cf8-4b66-b765-8aaef693125d
-- title:
--   Differentiable At Deriv At Zero
-- statement:
--   Definitions and structural lemmas for Differentiable At Deriv At Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/DifferentiableAtDerivAtZero.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Filter ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology Real
namespace GlobalTheory.JacobiDeriv
def derivAtZero (τ : ℂ) : ℂ := jacobiTheta₂' ((τ + 1) / 2) τ
open Complex Filter in
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology Real in
theorem _root_.GlobalTheory.JacobiDeriv.jacobiTheta₂_half_period (τ : ℂ) : jacobiTheta₂ ((τ + 1) / 2) τ = 0 := by
  have h1 := jacobiTheta₂_add_left' (-((τ + 1) / 2)) τ
  have h2 := jacobiTheta₂_add_left (-((τ + 1) / 2) + τ) τ
  rw [jacobiTheta₂_neg_left] at h1
  have e1 : -((τ + 1) / 2) + τ + 1 = (τ + 1) / 2 := by ring
  have e2 : -↑π * I * (τ + 2 * -((τ + 1) / 2)) = ↑π * I := by ring
  rw [e1, h1, e2, exp_pi_mul_I] at h2
  linear_combination h2 / 2
open Complex Filter in
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology Real in
lemma _root_.GlobalTheory.JacobiDeriv.derivAtZero_add_one (τ : ℂ) :
    _root_.GlobalTheory.JacobiDeriv.derivAtZero (τ + 1) = _root_.GlobalTheory.JacobiDeriv.derivAtZero τ := by
  unfold _root_.GlobalTheory.JacobiDeriv.derivAtZero jacobiTheta₂'
  congr 1
  ext n
  unfold jacobiTheta₂'_term jacobiTheta₂_term
  congr 1
  obtain ⟨m, hm⟩ := Int.even_mul_succ_self n
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨m, ?_⟩
  have hm' : ((n : ℂ) * (n + 1)) = (m : ℂ) + m := by exact_mod_cast hm
  linear_combination (π * I) * hm'
open Complex Filter in
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology Real in
lemma norm_jacobiTheta₂'_term_half_period_le {y : ℝ} (n : ℤ) {w : ℂ} (hy : 0 ≤ y)
    (hw : y ≤ w.im) :
    ‖jacobiTheta₂'_term n ((w + 1) / 2) w‖ ≤
      2 * π * (|n| ^ 1 * Real.exp (-π * (y * n ^ 2 - 2 * (y / 2) * |n|))) := by
  have him : ((w + 1) / 2).im = w.im / 2 := by simp
  rw [jacobiTheta₂'_term, norm_mul, norm_jacobiTheta₂_term, him]
  have h1 : ‖2 * (π : ℂ) * I * (n : ℂ)‖ = 2 * π * |(n : ℝ)| := by
    simp [abs_of_pos Real.pi_pos]
  rw [h1, pow_one, ← mul_assoc, Int.cast_abs]
  gcongr
  have hz : |n| ≤ n ^ 2 := by
    have := Int.le_self_sq |n|
    rwa [sq_abs] at this
  have hz' : (|n| : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hz
  have hn : 0 ≤ (n : ℝ) + |(n : ℝ)| := by
    have := neg_abs_le (n : ℝ)
    linarith
  have hwy : 0 ≤ w.im - y := by linarith
  rw [← Int.cast_abs] at hn hz' ⊢
  nlinarith [mul_nonneg hwy (by nlinarith : (0 : ℝ) ≤ (n : ℝ) ^ 2 + n), mul_nonneg hy hn,
    Real.pi_pos]
open Complex Filter in
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology Real in
lemma derivAtZero_eq_tsum_jacobiTheta₂'_term {w : ℂ} (hw : 0 < w.im) :
    _root_.GlobalTheory.JacobiDeriv.derivAtZero w = ∑' n : ℤ, jacobiTheta₂'_term n ((w + 1) / 2) w :=
  (hasSum_jacobiTheta₂'_term _ hw).tsum_eq.symm
open Complex Filter in
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology Real in
theorem _root_.GlobalTheory.JacobiDeriv.differentiableAt_derivAtZero {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ _root_.GlobalTheory.JacobiDeriv.derivAtZero τ := by
  have hy : 0 < τ.im / 2 := by linarith
  have hU : IsOpen {w : ℂ | τ.im / 2 < w.im} := isOpen_lt continuous_const continuous_im
  have hd : DifferentiableOn ℂ (fun w => ∑' n : ℤ, jacobiTheta₂'_term n ((w + 1) / 2) w)
      {w : ℂ | τ.im / 2 < w.im} := by
    refine differentiableOn_tsum_of_summable_norm
      ((summable_pow_mul_jacobiTheta₂_term_bound (τ.im / 2 / 2) hy 1).mul_left (2 * π))
      (fun n => ?_) hU (fun n w hw => norm_jacobiTheta₂'_term_half_period_le n hy.le (le_of_lt hw))
    unfold jacobiTheta₂'_term jacobiTheta₂_term
    fun_prop
  have hτU : τ ∈ {w : ℂ | τ.im / 2 < w.im} := by
    show τ.im / 2 < τ.im
    linarith
  refine (hd.differentiableAt (hU.mem_nhds hτU)).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_lt continuous_const continuous_im).mem_nhds (show (0 : ℝ) < τ.im from hτ)]
    with w hw
  exact derivAtZero_eq_tsum_jacobiTheta₂'_term hw
open Complex Filter in
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology Real in
theorem _root_.GlobalTheory.JacobiDeriv.tendsto_derivAtZero :
    Tendsto (fun τ : ℍ => _root_.GlobalTheory.JacobiDeriv.derivAtZero τ) UpperHalfPlane.atImInfty
      (𝓝 (2 * π * I)) := by
  have hg : (2 * π * I : ℂ) = ∑' n : ℤ, if n = -1 then 2 * π * I else 0 := by
    rw [tsum_ite_eq]
  rw [hg]
  refine Tendsto.congr (fun τ : ℍ => (derivAtZero_eq_tsum_jacobiTheta₂'_term τ.im_pos).symm) ?_
  have him : Tendsto (fun τ : ℍ => τ.im) UpperHalfPlane.atImInfty atTop := tendsto_comap
  refine tendsto_tsum_of_dominated_convergence
    ((summable_pow_mul_jacobiTheta₂_term_bound (1 / 2) one_pos 1).mul_left (2 * π))
    (fun n => ?_) ?_
  · split_ifs with hn
    · subst hn
      refine tendsto_const_nhds.congr fun τ => ?_
      have e : 2 * π * I * ((-1 : ℤ) : ℂ) * (((τ : ℂ) + 1) / 2) + π * I * ((-1 : ℤ) : ℂ) ^ 2 * τ
          = -(π * I) := by push_cast; ring
      simp only [jacobiTheta₂'_term, jacobiTheta₂_term, e, exp_neg, exp_pi_mul_I]
      push_cast
      ring
    · rcases eq_or_ne n 0 with h0 | h0
      · subst h0
        simp [jacobiTheta₂'_term]
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hpos : 0 < π * ((n : ℝ) ^ 2 + n) := by
        have h1 : (1 : ℤ) ≤ n ^ 2 + n := by
          rcases lt_or_gt_of_ne h0 with h | h
          · have : n ≤ -2 := by omega
            nlinarith
          · nlinarith
        have : (1 : ℝ) ≤ (n : ℝ) ^ 2 + n := by exact_mod_cast h1
        positivity
      have ht : Tendsto (fun τ : ℍ => 2 * π * |(n : ℝ)| *
          Real.exp (-(π * ((n : ℝ) ^ 2 + n) * τ.im))) UpperHalfPlane.atImInfty (𝓝 0) := by
        have := (Real.tendsto_exp_atBot.comp
          (tendsto_neg_atTop_atBot.comp (him.const_mul_atTop hpos))).const_mul (2 * π * |(n : ℝ)|)
        rw [mul_zero] at this
        exact this.congr fun τ => by simp [Function.comp_def, mul_assoc]
      refine ht.congr fun τ => ?_
      have hi : (((τ : ℂ) + 1) / 2).im = τ.im / 2 := by simp
      rw [jacobiTheta₂'_term, norm_mul, norm_jacobiTheta₂_term, hi]
      simp [abs_of_pos Real.pi_pos]
      left
      congr 1
      ring
  · rw [Filter.eventually_iff, UpperHalfPlane.atImInfty_mem]
    refine ⟨1, fun τ hτ n => ?_⟩
    have := norm_jacobiTheta₂'_term_half_period_le n zero_le_one hτ
    norm_num at this ⊢
    exact this
def eighthPower (τ : ℍ) : ℂ := cexp (2 * π * I * τ) * derivAtZero τ ^ 8
open Complex Filter in
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology Real in
lemma derivAtZero_neg_inv (τ : ℂ) (hτ : τ ≠ 0) :
    _root_.GlobalTheory.JacobiDeriv.derivAtZero (-τ)⁻¹ =
      -(1 / (-I * (-τ)⁻¹) ^ (1 / 2 : ℂ) * cexp (-π * I * (((-τ)⁻¹ + 1) / 2) ^ 2 / (-τ)⁻¹) /
        (-τ)⁻¹) * _root_.GlobalTheory.JacobiDeriv.derivAtZero τ := by
  unfold _root_.GlobalTheory.JacobiDeriv.derivAtZero
  rw [jacobiTheta₂'_functional_equation]
  have h1 : -1 / (-τ)⁻¹ = τ := by field_simp
  have h2 : ((-τ)⁻¹ + 1) / 2 / (-τ)⁻¹ = -((τ + 1) / 2) + 1 := by field_simp; ring
  rw [h1, h2, jacobiTheta₂'_add_left, jacobiTheta₂_add_left, jacobiTheta₂'_neg_left,
    jacobiTheta₂_neg_left, _root_.GlobalTheory.JacobiDeriv.jacobiTheta₂_half_period]
  ring
open Complex Filter in
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology Real in
lemma eighthPower_slash_S :
    _root_.GlobalTheory.JacobiDeriv.eighthPower ∣[(12 : ℤ)] ModularGroup.S =
      _root_.GlobalTheory.JacobiDeriv.eighthPower := by
  ext τ
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_S, UpperHalfPlane.modular_S_smul]
  unfold _root_.GlobalTheory.JacobiDeriv.eighthPower
  simp only [UpperHalfPlane.coe_mk]
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  set t : ℂ := (τ : ℂ) with ht
  rw [derivAtZero_neg_inv t hτ]
  have hc : ((-I * (-t)⁻¹) ^ (1 / 2 : ℂ)) ^ 8 = ((-t)⁻¹) ^ 4 := by
    have h := Complex.cpow_nat_inv_pow (-I * (-t)⁻¹) (n := 2) two_ne_zero
    rw [show ((2 : ℕ) : ℂ)⁻¹ = 1 / 2 by norm_num] at h
    rw [show (8 : ℕ) = 2 * 4 by rfl, pow_mul, h, mul_pow]
    rw [show (-I) ^ 4 = (1 : ℂ) by rw [neg_pow, I_pow_four]; norm_num, one_mul]
  have hE : cexp (-π * I * (((-t)⁻¹ + 1) / 2) ^ 2 / (-t)⁻¹) ^ 8 =
      cexp (8 * (-π * I * (((-t)⁻¹ + 1) / 2) ^ 2 / (-t)⁻¹)) := by
    rw [← Complex.exp_nat_mul]; norm_num
  have hsum : cexp (2 * π * I * (-t)⁻¹) * cexp (8 * (-π * I * (((-t)⁻¹ + 1) / 2) ^ 2 / (-t)⁻¹))
      = cexp (2 * π * I * t) := by
    rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨-2, ?_⟩
    field_simp
    push_cast
    ring
  have hpow : ((-t)⁻¹) ^ 12 * t ^ 12 = 1 := by
    rw [← mul_pow, inv_neg, neg_mul, inv_mul_cancel₀ hτ]; norm_num
  calc cexp (2 * π * I * (-t)⁻¹) *
        (-(1 / (-I * (-t)⁻¹) ^ (1 / 2 : ℂ) * cexp (-π * I * (((-t)⁻¹ + 1) / 2) ^ 2 / (-t)⁻¹) /
          (-t)⁻¹) * _root_.GlobalTheory.JacobiDeriv.derivAtZero t) ^ 8 * t ^ (-12 : ℤ)
      = (cexp (2 * π * I * (-t)⁻¹) * cexp (-π * I * (((-t)⁻¹ + 1) / 2) ^ 2 / (-t)⁻¹) ^ 8) *
          _root_.GlobalTheory.JacobiDeriv.derivAtZero t ^ 8 *
          (((-I * (-t)⁻¹) ^ (1 / 2 : ℂ)) ^ 8 * ((-t)⁻¹) ^ 8 * t ^ 12)⁻¹ := by
        rw [zpow_neg, zpow_ofNat]
        ring
    _ = cexp (2 * π * I * t) * _root_.GlobalTheory.JacobiDeriv.derivAtZero t ^ 8 := by
        rw [hE, hsum, hc, ← pow_add, hpow, inv_one, mul_one]
open Complex Filter in
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology Real in
lemma eighthPower_slash_T :
    _root_.GlobalTheory.JacobiDeriv.eighthPower ∣[(12 : ℤ)] ModularGroup.T =
      _root_.GlobalTheory.JacobiDeriv.eighthPower := by
  ext τ
  have hd : UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) ModularGroup.T)) ↑τ = 1 := by
    simp [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.map_apply_coe, ModularGroup.coe_T]
  rw [ModularForm.SL_slash_apply, hd, one_zpow, mul_one, UpperHalfPlane.modular_T_smul]
  unfold _root_.GlobalTheory.JacobiDeriv.eighthPower
  rw [UpperHalfPlane.coe_vadd, add_comm (((1 : ℝ) : ℂ)), Complex.ofReal_one,
    _root_.GlobalTheory.JacobiDeriv.derivAtZero_add_one, mul_add, Complex.exp_add, mul_one]
  have : cexp (2 * π * I) = 1 := Complex.exp_two_pi_mul_I
  rw [this, mul_one]
open Complex Filter in
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology Real in
theorem _root_.GlobalTheory.JacobiDeriv.eighthPower_slash (γ : SL(2, ℤ)) :
    _root_.GlobalTheory.JacobiDeriv.eighthPower ∣[(12 : ℤ)] γ = _root_.GlobalTheory.JacobiDeriv.eighthPower := by
  have hγ : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]; trivial
  induction hγ using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact eighthPower_slash_S
    · exact eighthPower_slash_T
  | one => exact SlashAction.slash_one _ _
  | mul x y _ _ hx hy => rw [SlashAction.slash_mul, hx, hy]
  | inv x _ hx =>
    conv_lhs => rw [← hx]
    rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
open Complex Filter in
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology Real in
theorem _root_.GlobalTheory.JacobiDeriv.qParam_one (τ : ℂ) : Function.Periodic.qParam 1 τ = cexp (2 * π * I * τ) := by
  simp [Function.Periodic.qParam]
def eighthPowerForm : CuspForm 𝒮ℒ 12 where
  toFun := eighthPower
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact eighthPower_slash A
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine DifferentiableOn.congr (f := fun z => cexp (2 * π * I * z) * derivAtZero z ^ 8)
      (fun z hz => ?_) fun z hz => ?_
    · exact (DifferentiableAt.mul (by fun_prop)
        ((differentiableAt_derivAtZero hz).pow 8)).differentiableWithinAt
    · simp [eighthPower, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [eighthPower_slash]
    have h := (UpperHalfPlane.qParam_tendsto_atImInfty zero_lt_one).mul (tendsto_derivAtZero.pow 8)
    rw [zero_mul] at h
    exact h.congr fun τ => by rw [qParam_one, eighthPower]
end GlobalTheory.JacobiDeriv


