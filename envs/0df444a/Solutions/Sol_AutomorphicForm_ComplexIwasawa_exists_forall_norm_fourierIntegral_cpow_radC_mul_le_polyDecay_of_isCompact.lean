-- Prove2me | solution 1 for AutomorphicForm.ComplexIwasawa.exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/75d6beb2-9932-5a69-8252-b34f95bb68b9

import Definitions.Def_AutomorphicForm_ComplexIwasawa
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Theorems.Thm_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact
import Theorems.Thm_AutomorphicForm_ComplexIwasawa_exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact

set_option autoImplicit false

open MeasureTheory AutomorphicForm.ComplexIwasawa
open scoped ContDiff FourierTransform

namespace B2bCKit

open VectorFourier

private theorem pow_mul_norm_fourierIntegral_le_of_coercive
    {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : V →L[ℝ] W →L[ℝ] ℝ)
    {μ : Measure V} [μ.IsAddHaarMeasure] {f : V → E} {n : ℕ} (hf : ContDiff ℝ n f)
    (h'f : ∀ j : ℕ, j ≤ n → Integrable (fun v => ‖iteratedFDeriv ℝ j f v‖) μ)
    {c : ℝ} (hc : 0 ≤ c) (hL : ∀ w : W, ∃ v : V, ‖v‖ ≤ 1 ∧ c * ‖w‖ ≤ ‖L v w‖) (w : W) :
    (c * ‖w‖) ^ n * ‖fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w‖
      ≤ 2 ^ n * ∑ j ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂μ := by
  obtain ⟨v, hv1, hvw⟩ := hL w
  have h'f' : ∀ (k j : ℕ), (k : ℕ∞) ≤ (0 : ℕ) → (j : ℕ∞) ≤ (n : ℕ) →
      Integrable (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ j f x‖) μ := by
    intro k j hk hj
    have hk0 : k = 0 := by exact_mod_cast (nonpos_iff_eq_zero.mp (by exact_mod_cast hk))
    subst hk0
    simpa using h'f j (by exact_mod_cast hj)
  have key := pow_mul_norm_iteratedFDeriv_fourierIntegral_le L (K := (0 : ℕ)) (N := (n : ℕ))
    (hf := hf) h'f' (k := 0) (n := n) le_rfl le_rfl v w
  rw [norm_iteratedFDeriv_zero, pow_zero, mul_one] at key
  have hsum : ∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (n + 1),
        ∫ x, ‖x‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f x‖ ∂μ
      = ∑ j ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ ∂μ := by
    rw [Finset.sum_product, zero_add, Finset.range_one, Finset.sum_singleton]
    simp
  rw [hsum] at key
  have hS : 0 ≤ ∑ j ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ ∂μ :=
    Finset.sum_nonneg fun j _ => integral_nonneg fun x => norm_nonneg _
  calc (c * ‖w‖) ^ n * ‖fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w‖
      ≤ |L v w| ^ n * ‖fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w‖ := by
        gcongr
        exact hvw.trans_eq (Real.norm_eq_abs _)
    _ ≤ ‖v‖ ^ n * (2 * 0 + 2) ^ n
          * ∑ j ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ ∂μ := by
        simpa using key
    _ ≤ 1 ^ n * (2 * 0 + 2) ^ n
          * ∑ j ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ ∂μ := by
        gcongr
    _ = 2 ^ n * ∑ j ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂μ := by norm_num

end B2bCKit

open scoped Nat in

theorem solution
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (h𝒢 : IsCompact 𝒢) (hdet : ∀ g ∈ 𝒢, g.det ≠ 0)
    (U : Set ℂ) (hU : IsCompact U) (hU2 : ∀ u ∈ U, 2 < u.re)
    (P : Matrix (Fin 2) (Fin 2) ℂ → ℂ → ℂ) (hPC : ∀ g ∈ 𝒢, ContDiff ℝ ∞ (P g))
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ z : ℂ, ‖iteratedFDeriv ℝ n (P g) z‖ ≤ C)
    (L : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hL : ∀ ξ : ℂ, ∃ v : ℂ, ‖v‖ ≤ 1 ∧ c * ‖ξ‖ ≤ ‖L v ξ‖)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ u ∈ U, ∀ ξ : ℂ,
      ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (fun z => ((radC g z : ℂ) ^ (-u)) * P g z) ξ‖
        ≤ C * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by

  rcases U.eq_empty_or_nonempty with hUe | hUne
  · exact ⟨1, one_pos, fun g _ u hu => by simp [hUe] at hu⟩

  obtain ⟨R, hR⟩ := hU.exists_bound_of_continuousOn (f := fun u : ℂ => u) continuousOn_id
  obtain ⟨u₀, hu₀U, hu₀⟩ := hU.exists_isMinOn hUne Complex.continuous_re.continuousOn
  set κ₀ : ℝ := u₀.re with hκ₀
  have hκ₀2 : 2 < κ₀ := hU2 u₀ hu₀U
  set κ₁ : ℝ := max κ₀ R with hκ₁

  choose Ch hCh using hPB
  have hW := fun n => AutomorphicForm.ComplexIwasawa.contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact
    𝒢 h𝒢 hdet U hU n
  have hWcd : ∀ g ∈ 𝒢, ∀ u : ℂ, ContDiff ℝ ∞ (fun z : ℂ => ((radC g z : ℂ) ^ (-u))) := (hW 0).1
  choose K hK0 hK using fun n => (hW n).2
  obtain ⟨J, hJ0, hJ⟩ := AutomorphicForm.ComplexIwasawa.exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact
    𝒢 h𝒢 hdet κ₀ κ₁ hκ₀2

  set D : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * K i * Ch (n - i) with hD
  have hCh0 : ∀ m, 0 ≤ Ch m := fun m => (hCh m).1.le
  have hD0 : ∀ n, 0 ≤ D n := fun n =>
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hK0 i).le) (hCh0 _)
  set M0' : ℝ := D 0 * J with hM0'
  set MN' : ℝ := 2 ^ N * ∑ j ∈ Finset.range (N + 1), D j * J with hMN'
  have hM0'0 : 0 ≤ M0' := mul_nonneg (hD0 0) hJ0.le
  have hMN'0 : 0 ≤ MN' := mul_nonneg (pow_nonneg (by norm_num) N)
    (Finset.sum_nonneg fun j _ => mul_nonneg (hD0 j) hJ0.le)
  refine ⟨(M0' * 2 ^ N + MN' * (2 / c) ^ N) + 1, by positivity, fun g hg u hu ξ => ?_⟩

  have huR : ‖u‖ ≤ R := by simpa using hR u hu
  have hure : κ₀ ≤ u.re := by have := hu₀ hu; simpa [hκ₀] using this
  have hure1 : u.re ≤ κ₁ := ((Complex.re_le_norm u).trans huR).trans (le_max_right _ _)
  have hrad0 : ∀ z : ℂ, 0 ≤ radC g z := fun z => Real.sqrt_nonneg _
  set f : ℂ → ℂ := fun z => ((radC g z : ℂ) ^ (-u)) * P g z with hfdef
  have hwC : ContDiff ℝ ∞ (fun z : ℂ => ((radC g z : ℂ) ^ (-u))) := hWcd g hg u
  have hCB : ∀ n z, ‖iteratedFDeriv ℝ n f z‖ ≤ D n * radC g z ^ (-u.re) := by
    intro n z
    refine (norm_iteratedFDeriv_mul_le hwC (hPC g hg) z (mod_cast le_top)).trans ?_
    rw [hD]
    dsimp only
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun z : ℂ => ((radC g z : ℂ) ^ (-u))) z‖
          * ‖iteratedFDeriv ℝ (n - i) (P g) z‖
        ≤ (n.choose i : ℝ) * (K i * radC g z ^ (-u.re)) * Ch (n - i) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (hK i g hg u hu z) (Nat.cast_nonneg _))
            ((hCh (n - i)).2 g hg z) (norm_nonneg _) ?_
          exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hK0 i).le (Real.rpow_nonneg (hrad0 z) _))
      _ = (n.choose i : ℝ) * K i * Ch (n - i) * radC g z ^ (-u.re) := by ring
  obtain ⟨hintr, hintJ⟩ := hJ g hg u.re hure hure1
  have hfC : ContDiff ℝ ∞ f := hwC.mul (hPC g hg)
  have hfCn : ContDiff ℝ (N : ℕ∞) f := hfC.of_le (mod_cast le_top)
  have h'f : ∀ j : ℕ, j ≤ N → Integrable (fun v => ‖iteratedFDeriv ℝ j f v‖) volume := by
    intro j _
    refine (hintr.const_mul (D j)).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact (hfC.continuous_iteratedFDeriv (mod_cast le_top)).norm.aestronglyMeasurable
    · rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact hCB j z
  have hIj : ∀ j, ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂volume ≤ D j * J := by
    intro j
    calc ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂volume ≤ ∫ v, D j * radC g v ^ (-u.re) ∂volume :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => norm_nonneg _) (hintr.const_mul _)
            (Filter.Eventually.of_forall (hCB j))
      _ = D j * ∫ v, radC g v ^ (-u.re) ∂volume := integral_const_mul _ _
      _ ≤ D j * J := mul_le_mul_of_nonneg_left hintJ (hD0 j)

  have key := B2bCKit.pow_mul_norm_fourierIntegral_le_of_coercive L (f := f) hfCn h'f hc.le hL
  set MN : ℝ := 2 ^ N * ∑ j ∈ Finset.range (N + 1), ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂volume with hMN
  have hMNle : MN ≤ MN' :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hIj j) (pow_nonneg (by norm_num) N)
  have hMN0 : (0 : ℝ) ≤ MN :=
    mul_nonneg (pow_nonneg (by norm_num) N)
      (Finset.sum_nonneg fun j _ => integral_nonneg fun v => norm_nonneg _)
  have hfint : Integrable f volume := by
    refine (hintr.const_mul (D 0)).mono' hfC.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    have h0 := hCB 0 z
    rwa [norm_iteratedFDeriv_zero] at h0
  set M0 : ℝ := ∫ v, ‖f v‖ ∂volume with hM0
  have hM00 : (0 : ℝ) ≤ M0 := integral_nonneg fun v => norm_nonneg _
  have hM0le : M0 ≤ M0' := by
    have := hIj 0
    simp only [norm_iteratedFDeriv_zero] at this
    exact this
  have hξ0 : (0 : ℝ) ≤ ‖ξ‖ := norm_nonneg _
  have h1ξ : (0 : ℝ) < 1 + ‖ξ‖ := by linarith
  have hrpow0 : (0 : ℝ) < (1 + ‖ξ‖) ^ (-(N : ℝ)) := Real.rpow_pos_of_pos h1ξ _
  have hc2 : (0 : ℝ) ≤ (2 / c) ^ N := pow_nonneg (div_nonneg (by norm_num) hc.le) N
  rcases lt_or_ge ‖ξ‖ 1 with hlt | hge
  · have hbd : (2 : ℝ) ^ (-(N : ℝ)) ≤ (1 + ‖ξ‖) ^ (-(N : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos h1ξ (by linarith) (neg_nonpos_of_nonneg (Nat.cast_nonneg N))
    have hstep1 : ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖ ≤ M0 :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    have hstep2 : (M0' : ℝ) = M0' * 2 ^ N * (2 : ℝ) ^ (-(N : ℝ)) := by
      rw [mul_assoc, show ((2 : ℝ) ^ N : ℝ) = (2 : ℝ) ^ (N : ℝ) from (Real.rpow_natCast 2 N).symm,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_neg_cancel, Real.rpow_zero, mul_one]
    have hstep3 : M0' * 2 ^ N * (2 : ℝ) ^ (-(N : ℝ)) ≤ M0' * 2 ^ N * (1 + ‖ξ‖) ^ (-(N : ℝ)) :=
      mul_le_mul_of_nonneg_left hbd (mul_nonneg hM0'0 (pow_nonneg (by norm_num) N))
    have hstep4 : (M0' * 2 ^ N : ℝ) ≤ M0' * 2 ^ N + MN' * (2 / c) ^ N + 1 := by
      have := mul_nonneg hMN'0 hc2; linarith
    calc ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖
        ≤ M0' := hstep1.trans hM0le
      _ = M0' * 2 ^ N * (2 : ℝ) ^ (-(N : ℝ)) := hstep2
      _ ≤ M0' * 2 ^ N * (1 + ‖ξ‖) ^ (-(N : ℝ)) := hstep3
      _ ≤ (M0' * 2 ^ N + MN' * (2 / c) ^ N + 1) * (1 + ‖ξ‖) ^ (-(N : ℝ)) :=
          mul_le_mul_of_nonneg_right hstep4 hrpow0.le
  · have hkey := key ξ
    have hcξ : (0 : ℝ) < c * ‖ξ‖ := mul_pos hc (by linarith)
    have hdiv : ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖ ≤ MN * (c * ‖ξ‖) ^ (-(N : ℝ)) := by
      rw [Real.rpow_neg hcξ.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hcξ N), mul_comm]
      exact hkey
    have h2 : (1 : ℝ) + ‖ξ‖ ≤ 2 * ‖ξ‖ := by linarith
    have hcmp : (c * ‖ξ‖) ^ (-(N : ℝ)) ≤ (2 / c) ^ N * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
      have hsplit : (c * ‖ξ‖ : ℝ) = (c / 2) * (2 * ‖ξ‖) := by ring
      rw [hsplit, Real.mul_rpow (div_nonneg hc.le (by norm_num)) (by linarith)]
      have hp1 : ((c / 2 : ℝ)) ^ (-(N : ℝ)) = (2 / c) ^ N := by
        rw [Real.rpow_neg (div_nonneg hc.le (by norm_num)), Real.rpow_natCast, ← inv_pow, inv_div]
      rw [hp1]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos h1ξ h2 (neg_nonpos_of_nonneg (Nat.cast_nonneg N))) hc2
    have hstep4 : (MN' * (2 / c) ^ N : ℝ) ≤ M0' * 2 ^ N + MN' * (2 / c) ^ N + 1 := by
      have := mul_nonneg hM0'0 (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) N); linarith
    calc ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖
        ≤ MN * (c * ‖ξ‖) ^ (-(N : ℝ)) := hdiv
      _ ≤ MN' * ((2 / c) ^ N * (1 + ‖ξ‖) ^ (-(N : ℝ))) :=
          mul_le_mul hMNle hcmp (Real.rpow_nonneg hcξ.le _) hMN'0
      _ = MN' * (2 / c) ^ N * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by ring
      _ ≤ (M0' * 2 ^ N + MN' * (2 / c) ^ N + 1) * (1 + ‖ξ‖) ^ (-(N : ℝ)) :=
          mul_le_mul_of_nonneg_right hstep4 hrpow0.le

end S_AutomorphicForm_ComplexIwasawa_exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact
end P2MW
export P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact (solution)
