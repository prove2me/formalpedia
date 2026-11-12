-- Prove2me | solution 1 for ALAVI.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T21:29:20.889962+00:00
-- url     : https://prove2.me/submissions/e903ccea-3085-4cab-98cc-32839001907a

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj
import Definitions.Def_ALAVI_Standing
import Definitions.Def_ALAVI_Params
import Definitions.Def_ALAVI_IsALAVIRun
import Definitions.Def_ALAVI_IsVIS
import Definitions.Def_ALAVI_IsMVIS
import Theorems.Thm_ALAVI_theorem_1_i
import Theorems.Thm_ALAVI_asymptotic_regularity
import Theorems.Thm_ALAVI_eq_32_optimality
import Theorems.Thm_ALAVI_eq_47
import Theorems.Thm_ALAVI_eq_51
import Theorems.Thm_ALAVI_lemma_4_1

namespace Aux_ALAVI_thm_1

lemma proj_mem {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (Ω : Set F) (hΩne : Ω.Nonempty) (hΩc : IsClosed Ω) (x : F) :
    CalamaiMore.Convergence.proj Ω x ∈ Ω := by
  unfold CalamaiMore.Convergence.proj CalamaiMore.Convergence.nearestPoint
  obtain ⟨y, hyΩ, hyd⟩ := hΩc.exists_infDist_eq_dist hΩne x
  have hex : ∃ z ∈ Ω, ∀ w ∈ Ω, ‖z - x‖ ≤ ‖w - x‖ := by
    refine ⟨y, hyΩ, fun w hw => ?_⟩
    have hw' : Metric.infDist x Ω ≤ dist x w := Metric.infDist_le_dist_of_mem hw
    rw [hyd, dist_comm x y, dist_comm x w, dist_eq_norm, dist_eq_norm] at hw'
    exact hw'
  rw [dif_pos hex]
  exact (Classical.choose_spec hex).1

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

lemma tendsto_of_norm_sub_tendsto_zero {X : Type*} [NormedAddCommGroup X]
    {x y : ℕ → X} {z : X}
    (hx : Filter.Tendsto x Filter.atTop (nhds z))
    (hdiff : Filter.Tendsto (fun n => ‖x n - y n‖) Filter.atTop (nhds 0)) :
    Filter.Tendsto y Filter.atTop (nhds z) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hx ⊢
  have hsum : Filter.Tendsto (fun n => ‖x n - y n‖ + ‖x n - z‖) Filter.atTop (nhds 0) := by
    simpa using hdiff.add hx
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => norm_nonneg _) (fun n => ?_)
  calc ‖y n - z‖ = ‖(y n - x n) + (x n - z)‖ := by congr 1; abel
    _ ≤ ‖y n - x n‖ + ‖x n - z‖ := norm_add_le _ _
    _ = ‖x n - y n‖ + ‖x n - z‖ := by rw [norm_sub_rev]

lemma tendsto_lipschitzOn {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {U : Set X} {F_map : X → Y} {K : ℝ}
    (hLip : ∀ a ∈ U, ∀ b ∈ U, ‖F_map a - F_map b‖ ≤ K * ‖a - b‖)
    {x : ℕ → X} {xbar : X} (hxU : ∀ n, x n ∈ U) (hxbarU : xbar ∈ U)
    (hx : Filter.Tendsto x Filter.atTop (nhds xbar)) :
    Filter.Tendsto (fun n => F_map (x n)) Filter.atTop (nhds (F_map xbar)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hx ⊢
  have hub : Filter.Tendsto (fun n => |K| * ‖x n - xbar‖) Filter.atTop (nhds 0) := by
    simpa using hx.const_mul |K|
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hub
    (fun _ => norm_nonneg _) (fun n => ?_)
  exact (hLip (x n) (hxU n) xbar hxbarU).trans
    (mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg _))

lemma isClosed_J_sublevel {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {J : E → EReal} (hJlsc : LowerSemicontinuous J) (c : ℝ) :
    IsClosed {z : E | J z ≤ (c : EReal)} := by
  have hpre : {z : E | J z ≤ (c : EReal)} =
      (fun z : E => (z, (c : EReal))) ⁻¹' {p : E × EReal | J p.1 ≤ p.2} := rfl
  rw [hpre]
  exact hJlsc.isClosed_epigraph.preimage (continuous_id.prodMk continuous_const)

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

end Aux_ALAVI_thm_1

open ALAVI

theorem solution {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (U : Set E) (C : ProperCone ℝ F) (G : E → E) (J : E → EReal) (Θ : E → F) (L τ η α γ : ℝ) (v u : ℕ → E) (p q : ℕ → F)
    (hA : Standing U C G J Θ L τ) (hP : Params η α γ L τ)
    (hrun : IsALAVIRun U C G J Θ η α γ v u p q)
    (hB : ∃ a b, IsMVIS U C G J Θ a b) :
    Bornology.IsBounded ((fun k => (v k, u k, p k)) '' Set.Ici 1) ∧
      (∀ (vbar ubar : E) (pbar : F),
        MapClusterPt (vbar, ubar, pbar) Filter.atTop (fun k => (v k, u k, p k)) →
          vbar = ubar ∧ IsVIS U C G J Θ ubar pbar) ∧
      (∀ (ubar : E) (pbar : F),
        MapClusterPt (ubar, ubar, pbar) Filter.atTop (fun k => (v k, u k, p k)) →
          IsMVIS U C G J Θ ubar pbar →
            Filter.Tendsto (fun k => (v k, u k, p k)) Filter.atTop (nhds (ubar, ubar, pbar))) ∧
      ((∀ (a : E) (b : F), IsVIS U C G J Θ a b → IsMVIS U C G J Θ a b) →
        ∃ (ubar : E) (pbar : F), IsVIS U C G J Θ ubar pbar ∧
          Filter.Tendsto (fun k => (v k, u k, p k)) Filter.atTop (nhds (ubar, ubar, pbar))) := by
  have hUc : IsClosed U := hA.1
  have hGLip : ∀ x ∈ U, ∀ y ∈ U, ‖G x - G y‖ ≤ L * ‖x - y‖ := hA.2.2.2.1
  have hJbot : ∀ y, J y ≠ ⊥ := hA.2.2.2.2.1.1
  have hJlsc : LowerSemicontinuous J := hA.2.2.2.2.1.2.2.2
  have hΘLip : ∀ x ∈ U, ∀ y ∈ U, ‖Θ x - Θ y‖ ≤ τ * ‖x - y‖ := hA.2.2.2.2.2.2.2
  have hη_lt : η < 1 := hP.2.1
  have hγ : 0 < γ := hP.2.2.1
  have hα : 0 < α := hP.2.2.2.2.1
  let Cstar : ProperCone ℝ F := ProperCone.innerDual (C : Set F)
  have h_part_i : Bornology.IsBounded ((fun k => (v k, u k, p k)) '' Set.Ici 1) :=
    ALAVI.theorem_1_i U C G J Θ L τ η α γ v u p q hA hP hrun hB
  obtain ⟨hv_step, hu_step, hp_step, hpq_step, _⟩ :=
    ALAVI.asymptotic_regularity U C G J Θ L τ η α γ v u p q hA hP hrun hB
  have hu_mem : ∀ m : ℕ, 2 ≤ m → u m ∈ U := by
    intro m hm
    have hr := hrun (m - 1) (by omega)
    have hmeq : m - 1 + 1 = m := by omega
    simpa [hmeq] using hr.2.2.1.1
  have hp_mem : ∀ m : ℕ, 2 ≤ m → p m ∈ (Cstar : Set F) := by
    intro m hm
    have hr := hrun (m - 1) (by omega)
    have hmeq : m - 1 + 1 = m := by omega
    have h := hr.2.2.2
    rw [hmeq] at h
    rw [h]
    exact Aux_ALAVI_thm_1.proj_mem (Cstar : Set F) Cstar.nonempty Cstar.isClosed _
  have hq_mem : ∀ m : ℕ, 1 ≤ m → q m ∈ (Cstar : Set F) := by
    intro m hm
    rw [(hrun m hm).2.1]
    exact Aux_ALAVI_thm_1.proj_mem (Cstar : Set F) Cstar.nonempty Cstar.isClosed _
  have huv_same : Filter.Tendsto (fun k => ‖v k - u k‖) Filter.atTop (nhds 0) := by
    have hub_lim : Filter.Tendsto (fun n => |η| / (1 - η) * ‖v n - v (n + 1)‖)
        Filter.atTop (nhds 0) := by
      have hv_s := (Filter.tendsto_add_atTop_iff_nat 1).mpr hv_step
      have h : Filter.Tendsto (fun n => ‖v n - v (n + 1)‖) Filter.atTop (nhds 0) := by
        simpa using hv_s
      simpa using h.const_mul (|η| / (1 - η))
    have hshift : Filter.Tendsto (fun n => ‖v (n + 1) - u (n + 1)‖) Filter.atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hub_lim
        (fun _ => norm_nonneg _) (fun n => ?_)
      have hv_rec := (hrun (n + 1) (by omega)).1
      have hsub : n + 1 - 1 = n := by omega
      rw [hsub] at hv_rec
      have hvec : (1 - η) • (v (n + 1) - u (n + 1)) = η • (v n - v (n + 1)) := by
        rw [hv_rec]
        module
      have hnorm := congrArg norm hvec
      rw [norm_smul, Real.norm_of_nonneg (by linarith : 0 ≤ 1 - η),
        norm_smul, Real.norm_eq_abs] at hnorm
      have hpos : 0 < 1 - η := by linarith
      have hne : 1 - η ≠ 0 := ne_of_gt hpos
      have hdiv : ‖v (n + 1) - u (n + 1)‖ = |η| / (1 - η) * ‖v n - v (n + 1)‖ := by
        field_simp
        linarith
      exact hdiv.le
    exact (Filter.tendsto_add_atTop_iff_nat 1).mp hshift
  have h_part_ii : ∀ (vbar ubar : E) (pbar : F),
      MapClusterPt (vbar, ubar, pbar) Filter.atTop (fun k => (v k, u k, p k)) →
        vbar = ubar ∧ IsVIS U C G J Θ ubar pbar := by
    intro vbar ubar pbar hcl
    obtain ⟨φ, hφ_mono, hφ_lim⟩ := hcl.tendsto_subseq
    let ψ : ℕ → ℕ := fun n => φ (n + 3)
    have hψ_ge3 : ∀ n : ℕ, 3 ≤ ψ n := fun n => (by omega : 3 ≤ n + 3).trans (hφ_mono.id_le _)
    have hψ_atTop : Filter.Tendsto ψ Filter.atTop Filter.atTop :=
      hφ_mono.tendsto_atTop.comp (Filter.tendsto_add_atTop_nat 3)
    have hψ_lim : Filter.Tendsto (fun n => (v (ψ n), u (ψ n), p (ψ n)))
        Filter.atTop (nhds (vbar, ubar, pbar)) :=
      (Filter.tendsto_add_atTop_iff_nat 3).mpr hφ_lim
    have hv_ψ : Filter.Tendsto (fun n => v (ψ n)) Filter.atTop (nhds vbar) :=
      (continuous_fst.tendsto _).comp hψ_lim
    have hu_ψ : Filter.Tendsto (fun n => u (ψ n)) Filter.atTop (nhds ubar) :=
      ((continuous_fst.comp continuous_snd).tendsto _).comp hψ_lim
    have hp_ψ : Filter.Tendsto (fun n => p (ψ n)) Filter.atTop (nhds pbar) :=
      ((continuous_snd.comp continuous_snd).tendsto _).comp hψ_lim
    have hv_eq_u : vbar = ubar := by
      have hu_ψ' : Filter.Tendsto (fun n => u (ψ n)) Filter.atTop (nhds vbar) :=
        Aux_ALAVI_thm_1.tendsto_of_norm_sub_tendsto_zero hv_ψ (huv_same.comp hψ_atTop)
      exact tendsto_nhds_unique hu_ψ' hu_ψ
    have hv_ψ_u : Filter.Tendsto (fun n => v (ψ n)) Filter.atTop (nhds ubar) := hv_eq_u ▸ hv_ψ
    refine ⟨hv_eq_u, ?_⟩
    have hubar_U : ubar ∈ U :=
      hUc.mem_of_tendsto hu_ψ (Filter.Eventually.of_forall fun n =>
        hu_mem (ψ n) (by linarith [hψ_ge3 n]))
    have hpbar_C : pbar ∈ ProperCone.innerDual (C : Set F) :=
      Cstar.isClosed.mem_of_tendsto hp_ψ
        (Filter.Eventually.of_forall fun n => hp_mem (ψ n) (by linarith [hψ_ge3 n]))
    have hdual_bar : ∀ p' ∈ ProperCone.innerDual (C : Set F),
        inner ℝ (Θ ubar) (p' - pbar) ≤ 0 := by
      intro p' hp'
      have hΘ_ψ : Filter.Tendsto (fun n => Θ (u (ψ n))) Filter.atTop (nhds (Θ ubar)) :=
        Aux_ALAVI_thm_1.tendsto_lipschitzOn hΘLip
          (fun n => hu_mem (ψ n) (by linarith [hψ_ge3 n])) hubar_U hu_ψ
      have hlhs_lim : Filter.Tendsto (fun n => inner ℝ (p' - p (ψ n)) (Θ (u (ψ n))))
          Filter.atTop (nhds (inner ℝ (p' - pbar) (Θ ubar))) :=
        (tendsto_const_nhds.sub hp_ψ).inner hΘ_ψ
      have hp_diff_ψ : Filter.Tendsto (fun n => ‖p (ψ n - 1) - p (ψ n)‖)
          Filter.atTop (nhds 0) := hp_step.comp hψ_atTop
      have hrhs_lim : Filter.Tendsto
          (fun n => 1 / γ * (‖p' - p (ψ n)‖ * ‖p (ψ n - 1) - p (ψ n)‖))
          Filter.atTop (nhds 0) := by
        have h1 : Filter.Tendsto (fun n => ‖p' - p (ψ n)‖) Filter.atTop (nhds ‖p' - pbar‖) :=
          (tendsto_const_nhds.sub hp_ψ).norm
        have h2 := (h1.mul hp_diff_ψ).const_mul (1 / γ)
        simpa using h2
      have hineq : ∀ n : ℕ, inner ℝ (p' - p (ψ n)) (Θ (u (ψ n))) ≤
          1 / γ * (‖p' - p (ψ n)‖ * ‖p (ψ n - 1) - p (ψ n)‖) := by
        intro n
        have h47 := (ALAVI.eq_47 U C G J Θ L τ η α γ v u p q hA hP hrun
          (ψ n) (by linarith [hψ_ge3 n]) p' hp').1
        have hcs : inner ℝ (p' - p (ψ n)) (p (ψ n) - p (ψ n - 1)) ≤
            ‖p' - p (ψ n)‖ * ‖p (ψ n - 1) - p (ψ n)‖ := by
          calc inner ℝ (p' - p (ψ n)) (p (ψ n) - p (ψ n - 1))
              ≤ ‖p' - p (ψ n)‖ * ‖p (ψ n) - p (ψ n - 1)‖ := real_inner_le_norm _ _
            _ = ‖p' - p (ψ n)‖ * ‖p (ψ n - 1) - p (ψ n)‖ := by
                rw [norm_sub_rev (p (ψ n)) (p (ψ n - 1))]
        have hm := mul_le_mul_of_nonneg_left hcs (by positivity : 0 ≤ 1 / γ)
        linarith
      have hlim_le := le_of_tendsto_of_tendsto hlhs_lim hrhs_lim (Filter.Eventually.of_forall hineq)
      rw [real_inner_comm] at hlim_le
      exact hlim_le
    rcases hB with ⟨a₀, b₀, hab₀⟩
    have hu_succ_ψ : Filter.Tendsto (fun n => u (ψ n + 1)) Filter.atTop (nhds ubar) := by
      have hu_s : Filter.Tendsto (fun k => ‖u k - u (k + 1)‖) Filter.atTop (nhds 0) := by
        have h := (Filter.tendsto_add_atTop_iff_nat 1).mpr hu_step
        simpa using h
      exact Aux_ALAVI_thm_1.tendsto_of_norm_sub_tendsto_zero hu_ψ (hu_s.comp hψ_atTop)
    have hq_ψ : Filter.Tendsto (fun n => q (ψ n)) Filter.atTop (nhds pbar) :=
      Aux_ALAVI_thm_1.tendsto_of_norm_sub_tendsto_zero hp_ψ (hpq_step.comp hψ_atTop)
    have hG_ψ : Filter.Tendsto (fun n => G (u (ψ n))) Filter.atTop (nhds (G ubar)) :=
      Aux_ALAVI_thm_1.tendsto_lipschitzOn hGLip
        (fun n => hu_mem (ψ n) (by linarith [hψ_ge3 n])) hubar_U hu_ψ
    have hΘ_succ_ψ : Filter.Tendsto (fun n => Θ (u (ψ n + 1))) Filter.atTop (nhds (Θ ubar)) :=
      Aux_ALAVI_thm_1.tendsto_lipschitzOn hΘLip
        (fun n => hu_mem (ψ n + 1) (by linarith [hψ_ge3 n])) hubar_U hu_succ_ψ
    have hJ_bound : ∀ w ∈ U, w ∈ GoldenRatioVI.Fixed.effDom J →
        J ubar ≤ ((inner ℝ (G ubar) (w - ubar) + (J w).toReal +
          inner ℝ pbar (Θ w - Θ ubar) : ℝ) : EReal) := by
      intro w hwU hwJ
      set Rw := inner ℝ (G ubar) (w - ubar) + (J w).toReal + inner ℝ pbar (Θ w - Θ ubar)
      have hrhs_w : Filter.Tendsto
          (fun n => inner ℝ (G (u (ψ n))) (w - u (ψ n + 1)) + (J w).toReal +
            inner ℝ (q (ψ n)) (Θ w - Θ (u (ψ n + 1))) +
            1 / α * inner ℝ (u (ψ n + 1) - v (ψ n)) (w - u (ψ n + 1)))
          Filter.atTop (nhds Rw) := by
        have ht1 : Filter.Tendsto (fun n => inner ℝ (G (u (ψ n))) (w - u (ψ n + 1)))
            Filter.atTop (nhds (inner ℝ (G ubar) (w - ubar))) :=
          hG_ψ.inner (tendsto_const_nhds.sub hu_succ_ψ)
        have ht2 : Filter.Tendsto (fun n => inner ℝ (q (ψ n)) (Θ w - Θ (u (ψ n + 1))))
            Filter.atTop (nhds (inner ℝ pbar (Θ w - Θ ubar))) :=
          hq_ψ.inner (tendsto_const_nhds.sub hΘ_succ_ψ)
        have ht3 : Filter.Tendsto
            (fun n => 1 / α * inner ℝ (u (ψ n + 1) - v (ψ n)) (w - u (ψ n + 1)))
            Filter.atTop (nhds (1 / α * inner ℝ (ubar - ubar) (w - ubar))) :=
          ((hu_succ_ψ.sub hv_ψ_u).inner (tendsto_const_nhds.sub hu_succ_ψ)).const_mul (1 / α)
        have hJW : Filter.Tendsto (fun _ : ℕ => (J w).toReal) Filter.atTop (nhds (J w).toReal) :=
          tendsto_const_nhds
        have hsum := ((ht1.add hJW).add ht2).add ht3
        simpa [Rw] using hsum
      have hfor_eps : ∀ ε : ℝ, 0 < ε → J ubar ≤ ((Rw + ε : ℝ) : EReal) := by
        intro ε hε
        have hev_lt : ∀ᶠ n in Filter.atTop,
            inner ℝ (G (u (ψ n))) (w - u (ψ n + 1)) + (J w).toReal +
              inner ℝ (q (ψ n)) (Θ w - Θ (u (ψ n + 1))) +
              1 / α * inner ℝ (u (ψ n + 1) - v (ψ n)) (w - u (ψ n + 1)) < Rw + ε :=
          hrhs_w.eventually (gt_mem_nhds (by linarith))
        have hev_mem : ∀ᶠ n in Filter.atTop,
            u (ψ n + 1) ∈ {z : E | J z ≤ ((Rw + ε : ℝ) : EReal)} := by
          refine hev_lt.mono fun n hn => ?_
          have hk1 : 1 ≤ ψ n := by linarith [hψ_ge3 n]
          have hsol := (ALAVI.eq_32_optimality U C G J Θ L τ α hA hα (G (u (ψ n))) (v (ψ n))
            (q (ψ n)) (hq_mem (ψ n) hk1) ⟨w, hwU, hwJ⟩ (u (ψ n + 1))).mp (hrun (ψ n) hk1).2.2.1
          have hvi := hsol.2.2 w hwU hwJ
          have hreal_le : (J (u (ψ n + 1))).toReal ≤ Rw + ε := by linarith
          show J (u (ψ n + 1)) ≤ ((Rw + ε : ℝ) : EReal)
          rw [← EReal.coe_toReal hsol.2.1 (hJbot _)]
          exact EReal.coe_le_coe_iff.mpr hreal_le
        exact (Aux_ALAVI_thm_1.isClosed_J_sublevel hJlsc (Rw + ε)).mem_of_tendsto
          hu_succ_ψ hev_mem
      have h1 := hfor_eps 1 zero_lt_one
      have hubar_J : ubar ∈ GoldenRatioVI.Fixed.effDom J := by
        intro htop
        rw [htop] at h1
        exact EReal.coe_ne_top _ (top_le_iff.mp h1)
      have hubar_eq : J ubar = ((J ubar).toReal : EReal) :=
        (EReal.coe_toReal hubar_J (hJbot ubar)).symm
      rw [hubar_eq]
      refine EReal.coe_le_coe_iff.mpr ?_
      by_contra hgt
      push_neg at hgt
      set ε := ((J ubar).toReal - Rw) / 2
      have hε : 0 < ε := by dsimp only [ε]; linarith
      have hle_eps := hfor_eps ε hε
      rw [hubar_eq] at hle_eps
      have hr := EReal.coe_le_coe_iff.mp hle_eps
      dsimp only [ε] at hr
      linarith
    have hubar_J : ubar ∈ GoldenRatioVI.Fixed.effDom J := by
      have h := hJ_bound a₀ hab₀.1 hab₀.2.1
      intro htop
      rw [htop] at h
      exact EReal.coe_ne_top _ (top_le_iff.mp h)
    refine ⟨hubar_U, hubar_J, hpbar_C, fun w hwU hwJ => ?_, hdual_bar⟩
    have hb := hJ_bound w hwU hwJ
    have hubar_eq : J ubar = ((J ubar).toReal : EReal) :=
      (EReal.coe_toReal hubar_J (hJbot ubar)).symm
    rw [hubar_eq] at hb
    have hr := EReal.coe_le_coe_iff.mp hb
    linarith
  have h_part_iii : ∀ (ubar : E) (pbar : F),
      MapClusterPt (ubar, ubar, pbar) Filter.atTop (fun k => (v k, u k, p k)) →
        IsMVIS U C G J Θ ubar pbar →
          Filter.Tendsto (fun k => (v k, u k, p k)) Filter.atTop (nhds (ubar, ubar, pbar)) := by
    intro ubar pbar hcl hmvis
    obtain ⟨φ, hφ_mono, hφ_lim⟩ := hcl.tendsto_subseq
    let ψ : ℕ → ℕ := fun n => φ (n + 3)
    have hψ_ge3 : ∀ n : ℕ, 3 ≤ ψ n := fun n => (by omega : 3 ≤ n + 3).trans (hφ_mono.id_le _)
    have hψ_atTop : Filter.Tendsto ψ Filter.atTop Filter.atTop :=
      hφ_mono.tendsto_atTop.comp (Filter.tendsto_add_atTop_nat 3)
    have hψ_lim : Filter.Tendsto (fun n => (v (ψ n), u (ψ n), p (ψ n)))
        Filter.atTop (nhds (ubar, ubar, pbar)) :=
      (Filter.tendsto_add_atTop_iff_nat 3).mpr hφ_lim
    have hv_ψ : Filter.Tendsto (fun n => v (ψ n)) Filter.atTop (nhds ubar) :=
      (continuous_fst.tendsto _).comp hψ_lim
    have hp_ψ : Filter.Tendsto (fun n => p (ψ n)) Filter.atTop (nhds pbar) :=
      ((continuous_snd.comp continuous_snd).tendsto _).comp hψ_lim
    have hp_prev_ψ : Filter.Tendsto (fun n => p (ψ n - 1)) Filter.atTop (nhds pbar) := by
      have hp_rev : Filter.Tendsto (fun n => ‖p (ψ n) - p (ψ n - 1)‖) Filter.atTop (nhds 0) := by
        refine (hp_step.comp hψ_atTop).congr fun n => ?_
        exact norm_sub_rev _ _
      exact Aux_ALAVI_thm_1.tendsto_of_norm_sub_tendsto_zero hp_ψ hp_rev
    have hlam_ψ_zero : Filter.Tendsto (fun n => lam η α γ L τ v u p (ψ n) ubar pbar)
        Filter.atTop (nhds 0) := by
      unfold lam
      have ht1 : Filter.Tendsto (fun n => 1 / (2 * α * (1 - η)) * ‖v (ψ n) - ubar‖ ^ 2)
          Filter.atTop (nhds 0) := by
        have hsub : Filter.Tendsto (fun n => v (ψ n) - ubar) Filter.atTop (nhds (ubar - ubar)) :=
          hv_ψ.sub tendsto_const_nhds
        have h := ((hsub.norm).pow 2).const_mul (1 / (2 * α * (1 - η)))
        simpa using h
      have ht2 : Filter.Tendsto
          (fun n => (γ * τ ^ 2 + L + τ) / 2 * ‖u (ψ n - 1) - u (ψ n)‖ ^ 2)
          Filter.atTop (nhds 0) := by
        have h := ((hu_step.comp hψ_atTop).pow 2).const_mul ((γ * τ ^ 2 + L + τ) / 2)
        simpa using h
      have ht3 : Filter.Tendsto (fun n => 1 / (2 * γ) * ‖p (ψ n - 1) - pbar‖ ^ 2)
          Filter.atTop (nhds 0) := by
        have hsub : Filter.Tendsto (fun n => p (ψ n - 1) - pbar) Filter.atTop (nhds (pbar - pbar)) :=
          hp_prev_ψ.sub tendsto_const_nhds
        have h := ((hsub.norm).pow 2).const_mul (1 / (2 * γ))
        simpa using h
      simpa using (ht1.add ht2).add ht3
    have hrho_pos : 0 < rho η α γ τ :=
      (ALAVI.lemma_4_1 U C G J Θ L τ η α γ v u p q hA hP hrun 3 (by omega)
        (hu_mem 2 (by omega)) ubar hmvis.1 hmvis.2.1 pbar hmvis.2.2.1 ubar).1
    let L_seq : ℕ → ℝ := fun n => lam η α γ L τ v u p (n + 3) ubar pbar
    have hL_anti : Antitone L_seq := by
      refine antitone_nat_of_succ_le fun n => ?_
      have h51 := ALAVI.eq_51 U C G J Θ L τ η α γ v u p q hA hP hrun (n + 3) (by omega)
        (hu_mem (n + 3 - 1) (by omega)) ubar pbar hmvis
      have hnn : 0 ≤ rho η α γ τ *
          (‖v (n + 3 - 1) - v (n + 3)‖ ^ 2 + ‖u (n + 3 - 1) - u (n + 3)‖ ^ 2 +
            ‖p (n + 3 - 1) - p (n + 3)‖ ^ 2 + ‖p (n + 3) - q (n + 3)‖ ^ 2) :=
        mul_nonneg hrho_pos.le (by positivity)
      have heq : n + 1 + 3 = n + 3 + 1 := by omega
      dsimp only [L_seq]
      rw [heq]
      linarith
    have hL_bdd : BddBelow (Set.range L_seq) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact Aux_ALAVI_thm_1.lam_nonneg hA hP v u p (n + 3) ubar pbar
    have hL_lim : Filter.Tendsto L_seq Filter.atTop (nhds (⨅ i, L_seq i)) :=
      tendsto_atTop_ciInf hL_anti hL_bdd
    have hψ_sub3_atTop : Filter.Tendsto (fun n => ψ n - 3) Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop]
      intro B
      filter_upwards [(Filter.tendsto_atTop.mp hψ_atTop) (B + 3)] with n hn
      omega
    have hL_subseq : Filter.Tendsto (fun n => L_seq (ψ n - 3)) Filter.atTop (nhds (⨅ i, L_seq i)) :=
      hL_lim.comp hψ_sub3_atTop
    have hL_subseq_eq : (fun n => L_seq (ψ n - 3)) = (fun n => lam η α γ L τ v u p (ψ n) ubar pbar) := by
      ext n
      dsimp only [L_seq]
      rw [Nat.sub_add_cancel (hψ_ge3 n)]
    rw [hL_subseq_eq] at hL_subseq
    have hiInf_zero : (⨅ i, L_seq i) = 0 := tendsto_nhds_unique hL_subseq hlam_ψ_zero
    rw [hiInf_zero] at hL_lim
    have hlam_zero : Filter.Tendsto (fun k => lam η α γ L τ v u p k ubar pbar)
        Filter.atTop (nhds 0) :=
      (Filter.tendsto_add_atTop_iff_nat 3).mp hL_lim
    have hL_nonneg : 0 ≤ L := hA.2.2.1
    have hτ : 0 < τ := hA.2.2.2.2.2.2.1
    have hv_norm_zero : Filter.Tendsto (fun k => ‖v k - ubar‖) Filter.atTop (nhds 0) := by
      refine Aux_ALAVI_thm_1.tendsto_zero_of_sq_le (fun _ => norm_nonneg _)
        (s := fun k => 2 * α * (1 - η) * lam η α γ L τ v u p k ubar pbar) (fun k => ?_) ?_
      · have hgt : 0 ≤ γ * τ ^ 2 := mul_nonneg hγ.le (sq_nonneg _)
        have ht2 : 0 ≤ (γ * τ ^ 2 + L + τ) / 2 * ‖u (k - 1) - u k‖ ^ 2 :=
          mul_nonneg (div_nonneg (by linarith) (by norm_num)) (sq_nonneg _)
        have ht3 : 0 ≤ 1 / (2 * γ) * ‖p (k - 1) - pbar‖ ^ 2 :=
          mul_nonneg (div_nonneg zero_le_one (by linarith)) (sq_nonneg _)
        have h1 : 1 / (2 * α * (1 - η)) * ‖v k - ubar‖ ^ 2 ≤ lam η α γ L τ v u p k ubar pbar := by
          unfold lam; linarith
        have hc_pos : 0 < 2 * α * (1 - η) := mul_pos (by linarith) (by linarith)
        have hm := mul_le_mul_of_nonneg_left h1 hc_pos.le
        have hα_ne : α ≠ 0 := ne_of_gt hα
        have h1mη_ne : 1 - η ≠ 0 := by linarith
        have hid : 2 * α * (1 - η) * (1 / (2 * α * (1 - η)) * ‖v k - ubar‖ ^ 2) =
            ‖v k - ubar‖ ^ 2 := by field_simp
        linarith
      · simpa using hlam_zero.const_mul (2 * α * (1 - η))
    have hv_conv : Filter.Tendsto v Filter.atTop (nhds ubar) :=
      tendsto_iff_norm_sub_tendsto_zero.mpr hv_norm_zero
    have hu_conv : Filter.Tendsto u Filter.atTop (nhds ubar) :=
      Aux_ALAVI_thm_1.tendsto_of_norm_sub_tendsto_zero hv_conv huv_same
    have hp_prev_norm_zero : Filter.Tendsto (fun k => ‖p (k - 1) - pbar‖) Filter.atTop (nhds 0) := by
      refine Aux_ALAVI_thm_1.tendsto_zero_of_sq_le (fun _ => norm_nonneg _)
        (s := fun k => 2 * γ * lam η α γ L τ v u p k ubar pbar) (fun k => ?_) ?_
      · have hgt : 0 ≤ γ * τ ^ 2 := mul_nonneg hγ.le (sq_nonneg _)
        have ht1 : 0 ≤ 1 / (2 * α * (1 - η)) * ‖v k - ubar‖ ^ 2 :=
          mul_nonneg (div_nonneg zero_le_one (mul_nonneg (by linarith) (by linarith))) (sq_nonneg _)
        have ht2 : 0 ≤ (γ * τ ^ 2 + L + τ) / 2 * ‖u (k - 1) - u k‖ ^ 2 :=
          mul_nonneg (div_nonneg (by linarith) (by norm_num)) (sq_nonneg _)
        have h3 : 1 / (2 * γ) * ‖p (k - 1) - pbar‖ ^ 2 ≤ lam η α γ L τ v u p k ubar pbar := by
          unfold lam; linarith
        have hc_pos : 0 < 2 * γ := by linarith
        have hm := mul_le_mul_of_nonneg_left h3 hc_pos.le
        have hγ_ne : γ ≠ 0 := ne_of_gt hγ
        have hid : 2 * γ * (1 / (2 * γ) * ‖p (k - 1) - pbar‖ ^ 2) = ‖p (k - 1) - pbar‖ ^ 2 := by
          field_simp
        linarith
      · simpa using hlam_zero.const_mul (2 * γ)
    have hp_norm_zero : Filter.Tendsto (fun k => ‖p k - pbar‖) Filter.atTop (nhds 0) := by
      have h := (Filter.tendsto_add_atTop_iff_nat 1).mpr hp_prev_norm_zero
      simpa using h
    have hp_conv : Filter.Tendsto p Filter.atTop (nhds pbar) :=
      tendsto_iff_norm_sub_tendsto_zero.mpr hp_norm_zero
    exact hv_conv.prodMk_nhds (hu_conv.prodMk_nhds hp_conv)
  have h_part_iiip : (∀ (a : E) (b : F), IsVIS U C G J Θ a b → IsMVIS U C G J Θ a b) →
      ∃ (ubar : E) (pbar : F), IsVIS U C G J Θ ubar pbar ∧
        Filter.Tendsto (fun k => (v k, u k, p k)) Filter.atTop (nhds (ubar, ubar, pbar)) := by
    intro hvis_to_mvis
    let S : Set (E × E × F) := (fun k => (v k, u k, p k)) '' Set.Ici 1
    have hK_compact : IsCompact (closure S) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_closure h_part_i.closure
    have hseq_mem : ∀ n : ℕ, (v (n + 1), u (n + 1), p (n + 1)) ∈ closure S :=
      fun n => subset_closure ⟨n + 1, by simp, rfl⟩
    obtain ⟨⟨vbar, ubar, pbar⟩, _, φ, hφ_mono, hφ_lim⟩ := hK_compact.tendsto_subseq hseq_mem
    have hψ_mono : StrictMono (fun n => φ n + 1) := fun i j hij =>
      Nat.add_lt_add_right (hφ_mono hij) 1
    have hcl : MapClusterPt (vbar, ubar, pbar) Filter.atTop (fun k => (v k, u k, p k)) :=
      MapClusterPt.of_comp hψ_mono.tendsto_atTop hφ_lim.mapClusterPt
    obtain ⟨hv_eq, hvis⟩ := h_part_ii vbar ubar pbar hcl
    have hcl_u : MapClusterPt (ubar, ubar, pbar) Filter.atTop (fun k => (v k, u k, p k)) :=
      hv_eq ▸ hcl
    have hmvis : IsMVIS U C G J Θ ubar pbar := hvis_to_mvis ubar pbar hvis
    exact ⟨ubar, pbar, hvis, h_part_iii ubar pbar hcl_u hmvis⟩
  exact ⟨h_part_i, h_part_ii, h_part_iii, h_part_iiip⟩
