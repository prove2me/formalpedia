-- Prove2me | solution 1 for ALAVI.asymptotic_regularity
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T21:26:17.652198+00:00
-- url     : https://prove2.me/submissions/b17d293a-6d2f-4f0c-b4f9-9e00a78d77d8

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj
import Definitions.Def_ALAVI_Standing
import Definitions.Def_ALAVI_Params
import Definitions.Def_ALAVI_IsALAVIRun
import Definitions.Def_ALAVI_IsMVIS
import Theorems.Thm_ALAVI_eq_51
import Theorems.Thm_ALAVI_lemma_4_1

namespace Aux_ALAVI_asymp

lemma lam_nonneg {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set E} {C : ProperCone ℝ F} {G : E → E} {J : E → EReal} {Θ : E → F}
    {η α γ L τ : ℝ} (hA : ALAVI.Standing U C G J Θ L τ)
    (hP : ALAVI.Params η α γ L τ) (v u : ℕ → E) (p : ℕ → F) (k : ℕ) (a : E) (b : F) :
    0 ≤ ALAVI.lam η α γ L τ v u p k a b := by
  have hL : 0 ≤ L := hA.2.2.1
  have hτ : 0 < τ := hA.2.2.2.2.2.2.1
  have hη_lt : η < 1 := hP.2.1
  have hγ : 0 < γ := hP.2.2.1
  have hα : 0 < α := hP.2.2.2.2.1
  unfold ALAVI.lam
  have h1 : 0 ≤ 1 / (2 * α * (1 - η)) * ‖v k - a‖ ^ 2 :=
    mul_nonneg (div_nonneg zero_le_one (mul_nonneg (by linarith) (by linarith))) (sq_nonneg _)
  have h2 : 0 ≤ (γ * τ ^ 2 + L + τ) / 2 * ‖u (k - 1) - u k‖ ^ 2 := by
    have hgt : 0 ≤ γ * τ ^ 2 := mul_nonneg hγ.le (sq_nonneg _)
    exact mul_nonneg (div_nonneg (by linarith) (by norm_num)) (sq_nonneg _)
  have h3 : 0 ≤ 1 / (2 * γ) * ‖p (k - 1) - b‖ ^ 2 :=
    mul_nonneg (div_nonneg zero_le_one (by linarith)) (sq_nonneg _)
  linarith

lemma tendsto_zero_of_sq_le {f s : ℕ → ℝ} (hf_nonneg : ∀ k, 0 ≤ f k)
    (hle : ∀ k, f k ^ 2 ≤ s k) (hs : Filter.Tendsto s Filter.atTop (nhds 0)) :
    Filter.Tendsto f Filter.atTop (nhds 0) := by
  have hsq : Filter.Tendsto (fun k => f k ^ 2) Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs
      (fun k => sq_nonneg (f k)) hle
  have hsqrt : Filter.Tendsto (fun k => Real.sqrt (f k ^ 2)) Filter.atTop (nhds (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun k => ?_
  exact Real.sqrt_sq (hf_nonneg k)

end Aux_ALAVI_asymp

open ALAVI

theorem solution {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (U : Set E) (C : ProperCone ℝ F) (G : E → E) (J : E → EReal) (Θ : E → F) (L τ η α γ : ℝ) (v u : ℕ → E) (p q : ℕ → F)
    (hA : Standing U C G J Θ L τ) (hP : Params η α γ L τ)
    (hrun : IsALAVIRun U C G J Θ η α γ v u p q)
    (hB : ∃ a b, IsMVIS U C G J Θ a b) :
    Filter.Tendsto (fun k => ‖v (k - 1) - v k‖) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun k => ‖u (k - 1) - u k‖) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun k => ‖p (k - 1) - p k‖) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun k => ‖p k - q k‖) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun k => ‖u k - v (k + 1)‖) Filter.atTop (nhds 0) := by
  rcases hB with ⟨a, b, hab⟩
  have hη_lt : η < 1 := hP.2.1
  have hu_mem : ∀ m : ℕ, 2 ≤ m → u m ∈ U := by
    intro m hm
    have hr := hrun (m - 1) (by omega)
    have hmeq : m - 1 + 1 = m := by omega
    simpa [hmeq] using hr.2.2.1.1
  have hrho_pos : 0 < rho η α γ τ :=
    (ALAVI.lemma_4_1 U C G J Θ L τ η α γ v u p q hA hP hrun 3 (by omega)
      (hu_mem 2 (by omega)) a hab.1 hab.2.1 b hab.2.2.1 a).1
  let s : ℕ → ℝ := fun k =>
    ‖v (k - 1) - v k‖ ^ 2 + ‖u (k - 1) - u k‖ ^ 2 + ‖p (k - 1) - p k‖ ^ 2 + ‖p k - q k‖ ^ 2
  let L_seq : ℕ → ℝ := fun n => lam η α γ L τ v u p (n + 3) a b
  have hstep_le : ∀ n : ℕ,
      rho η α γ τ * s (n + 3) ≤ L_seq n - L_seq (n + 1) := by
    intro n
    have h51 := ALAVI.eq_51 U C G J Θ L τ η α γ v u p q hA hP hrun (n + 3) (by omega)
      (hu_mem (n + 3 - 1) (by omega)) a b hab
    have heq : n + 1 + 3 = n + 3 + 1 := by omega
    dsimp only [L_seq, s]
    rw [heq]
    exact h51
  have hL_anti : Antitone L_seq := by
    refine antitone_nat_of_succ_le fun n => ?_
    have hs_nn : 0 ≤ rho η α γ τ * s (n + 3) :=
      mul_nonneg hrho_pos.le (by dsimp only [s]; positivity)
    linarith [hstep_le n]
  have hL_bdd : BddBelow (Set.range L_seq) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact Aux_ALAVI_asymp.lam_nonneg hA hP v u p (n + 3) a b
  have hL_lim : Filter.Tendsto L_seq Filter.atTop (nhds (⨅ i, L_seq i)) :=
    tendsto_atTop_ciInf hL_anti hL_bdd
  have hL_succ_lim : Filter.Tendsto (fun n => L_seq (n + 1)) Filter.atTop (nhds (⨅ i, L_seq i)) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mpr hL_lim
  have hdiff_lim : Filter.Tendsto (fun n => (L_seq n - L_seq (n + 1)) / rho η α γ τ)
      Filter.atTop (nhds 0) := by
    have h := (hL_lim.sub hL_succ_lim).div_const (rho η α γ τ)
    simpa using h
  have hs_shift_lim : Filter.Tendsto (fun n => s (n + 3)) Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiff_lim
      (fun n => by dsimp only [s]; positivity) (fun n => ?_)
    exact (le_div_iff₀' hrho_pos).mpr (hstep_le n)
  have hs_lim : Filter.Tendsto s Filter.atTop (nhds 0) :=
    (Filter.tendsto_add_atTop_iff_nat 3).mp hs_shift_lim
  have hv_lim : Filter.Tendsto (fun k => ‖v (k - 1) - v k‖) Filter.atTop (nhds 0) := by
    refine Aux_ALAVI_asymp.tendsto_zero_of_sq_le (fun _ => norm_nonneg _) (fun k => ?_) hs_lim
    dsimp only [s]
    linarith [sq_nonneg ‖u (k - 1) - u k‖, sq_nonneg ‖p (k - 1) - p k‖, sq_nonneg ‖p k - q k‖]
  have hu_lim : Filter.Tendsto (fun k => ‖u (k - 1) - u k‖) Filter.atTop (nhds 0) := by
    refine Aux_ALAVI_asymp.tendsto_zero_of_sq_le (fun _ => norm_nonneg _) (fun k => ?_) hs_lim
    dsimp only [s]
    linarith [sq_nonneg ‖v (k - 1) - v k‖, sq_nonneg ‖p (k - 1) - p k‖, sq_nonneg ‖p k - q k‖]
  have hp_lim : Filter.Tendsto (fun k => ‖p (k - 1) - p k‖) Filter.atTop (nhds 0) := by
    refine Aux_ALAVI_asymp.tendsto_zero_of_sq_le (fun _ => norm_nonneg _) (fun k => ?_) hs_lim
    dsimp only [s]
    linarith [sq_nonneg ‖v (k - 1) - v k‖, sq_nonneg ‖u (k - 1) - u k‖, sq_nonneg ‖p k - q k‖]
  have hpq_lim : Filter.Tendsto (fun k => ‖p k - q k‖) Filter.atTop (nhds 0) := by
    refine Aux_ALAVI_asymp.tendsto_zero_of_sq_le (fun _ => norm_nonneg _) (fun k => ?_) hs_lim
    dsimp only [s]
    linarith [sq_nonneg ‖v (k - 1) - v k‖, sq_nonneg ‖u (k - 1) - u k‖, sq_nonneg ‖p (k - 1) - p k‖]
  have huv_lim : Filter.Tendsto (fun k => ‖u k - v (k + 1)‖) Filter.atTop (nhds 0) := by
    have hu_succ : Filter.Tendsto (fun k => ‖u k - u (k + 1)‖) Filter.atTop (nhds 0) := by
      have h := (Filter.tendsto_add_atTop_iff_nat 1).mpr hu_lim
      simpa using h
    have hv_succ : Filter.Tendsto (fun k => ‖v k - v (k + 1)‖) Filter.atTop (nhds 0) := by
      have h := (Filter.tendsto_add_atTop_iff_nat 1).mpr hv_lim
      simpa using h
    have hub_lim : Filter.Tendsto
        (fun k => ‖u (k + 1) - u (k + 2)‖ + |η| / (1 - η) * ‖v (k + 1) - v (k + 2)‖)
        Filter.atTop (nhds 0) := by
      have hu2 := (Filter.tendsto_add_atTop_iff_nat 1).mpr hu_succ
      have hv2 := (Filter.tendsto_add_atTop_iff_nat 1).mpr hv_succ
      have h := hu2.add (hv2.const_mul (|η| / (1 - η)))
      simpa using h
    have huv_shift : Filter.Tendsto (fun k => ‖u (k + 1) - v (k + 2)‖) Filter.atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hub_lim
        (fun _ => norm_nonneg _) (fun k => ?_)
      have hv_rec := (hrun (k + 2) (by omega)).1
      have hk2_sub : k + 2 - 1 = k + 1 := by omega
      rw [hk2_sub] at hv_rec
      have hvec : (1 - η) • (u (k + 1) - v (k + 2)) =
          (1 - η) • (u (k + 1) - u (k + 2)) - η • (v (k + 1) - v (k + 2)) := by
        rw [hv_rec, smul_sub, smul_sub, smul_add, smul_smul, smul_smul, sub_smul, one_smul]
        module
      have hnorm := congrArg norm hvec
      rw [norm_smul, Real.norm_of_nonneg (by linarith : 0 ≤ 1 - η)] at hnorm
      have htri : ‖(1 - η) • (u (k + 1) - u (k + 2)) - η • (v (k + 1) - v (k + 2))‖ ≤
          (1 - η) * ‖u (k + 1) - u (k + 2)‖ + |η| * ‖v (k + 1) - v (k + 2)‖ := by
        calc ‖(1 - η) • (u (k + 1) - u (k + 2)) - η • (v (k + 1) - v (k + 2))‖
            ≤ ‖(1 - η) • (u (k + 1) - u (k + 2))‖ + ‖η • (v (k + 1) - v (k + 2))‖ :=
              norm_sub_le _ _
          _ = (1 - η) * ‖u (k + 1) - u (k + 2)‖ + |η| * ‖v (k + 1) - v (k + 2)‖ := by
              rw [norm_smul, Real.norm_of_nonneg (by linarith : 0 ≤ 1 - η),
                norm_smul, Real.norm_eq_abs]
      have hle1 : (1 - η) * ‖u (k + 1) - v (k + 2)‖ ≤
          (1 - η) * ‖u (k + 1) - u (k + 2)‖ + |η| * ‖v (k + 1) - v (k + 2)‖ := by linarith
      have hpos : 0 < 1 - η := by linarith
      have hdiv := (le_div_iff₀' hpos).mpr hle1
      have hne : 1 - η ≠ 0 := ne_of_gt hpos
      have hrhs : ((1 - η) * ‖u (k + 1) - u (k + 2)‖ + |η| * ‖v (k + 1) - v (k + 2)‖) / (1 - η) =
          ‖u (k + 1) - u (k + 2)‖ + |η| / (1 - η) * ‖v (k + 1) - v (k + 2)‖ := by
        field_simp
      linarith
    exact (Filter.tendsto_add_atTop_iff_nat 1).mp huv_shift
  exact ⟨hv_lim, hu_lim, hp_lim, hpq_lim, huv_lim⟩
