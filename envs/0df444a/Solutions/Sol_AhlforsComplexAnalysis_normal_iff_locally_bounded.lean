-- Prove2me | solution 1 for AhlforsComplexAnalysis.normal_iff_locally_bounded
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T13:26:11.812392+00:00
-- url     : https://prove2.me/submissions/15d011e0-c5a1-4817-a99a-cecceed8eb0e

import Definitions.Def_AhlforsComplexAnalysis_Defs
import Mathlib

open AhlforsComplexAnalysis
open Metric Set Filter Topology

namespace AhlforsMontel

open AhlforsComplexAnalysis

/-- local uniform Lipschitz bound from Cauchy estimates -/
lemma equi {Ω : Set ℂ} (hΩ : IsOpen Ω) {𝔉 : Set (ℂ → ℂ)}
    (hanal : ∀ f ∈ 𝔉, AnalyticOnNhd ℂ f Ω)
    (hbd : ∀ K ⊆ Ω, IsCompact K → ∃ M : ℝ, ∀ f ∈ 𝔉, ∀ z ∈ K, ‖f z‖ ≤ M)
    {K : Set ℂ} (hK : K ⊆ Ω) (hKc : IsCompact K) :
    ∃ δ > 0, ∃ L ≥ 0, ∀ f ∈ 𝔉, ∀ z ∈ K, ∀ w, ‖w - z‖ < δ →
      w ∈ Ω ∧ ‖f w - f z‖ ≤ L * ‖w - z‖ := by
  obtain ⟨δ0, hδ0, hsub⟩ := hKc.exists_cthickening_subset_open hΩ hK
  obtain ⟨M0, hM0⟩ := hbd _ (hsub) hKc.cthickening
  set M := max M0 0 with hM
  have hMb : ∀ f ∈ 𝔉, ∀ x ∈ cthickening δ0 K, ‖f x‖ ≤ M :=
    fun f hf x hx => (hM0 f hf x hx).trans (le_max_left _ _)
  set δ := δ0 / 2 with hδ
  have hδpos : 0 < δ := by positivity
  refine ⟨δ, hδpos, 2 * M / δ, by positivity, fun f hf z hz w hw => ?_⟩
  have hball : ∀ x ∈ ball z (2 * δ), x ∈ cthickening δ0 K := fun x hx =>
    mem_cthickening_of_dist_le x z δ0 K hz (by rw [mem_ball] at hx; linarith)
  have hwΩ : w ∈ Ω := hsub (hball w (by rw [mem_ball, dist_eq_norm]; linarith))
  refine ⟨hwΩ, ?_⟩
  have hdiff : ∀ x ∈ ball z (2 * δ), DifferentiableAt ℂ f x := fun x hx =>
    (hanal f hf x (hsub (hball x hx))).differentiableAt
  have hderiv : ∀ ζ ∈ ball z δ, ‖deriv f ζ‖ ≤ 2 * M / δ := by
    intro ζ hζ
    have hsubb : ball ζ δ ⊆ ball z (2 * δ) := by
      intro x hx; rw [mem_ball] at hx hζ ⊢
      linarith [dist_triangle x ζ z]
    refine Complex.norm_deriv_le_div_of_mapsTo_ball
      (fun x hx => (hdiff x (hsubb hx)).differentiableWithinAt) (fun x hx => ?_) hδpos
    rw [mem_closedBall, dist_eq_norm]
    have h1 := hMb f hf x (hball x (hsubb hx))
    have h2 := hMb f hf ζ (hball ζ (hsubb (mem_ball_self hδpos)))
    calc ‖f x - f ζ‖ ≤ ‖f x‖ + ‖f ζ‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith
  have := (convex_ball z δ).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => hdiff x (ball_subset_ball (by linarith) hx)) hderiv (mem_ball_self hδpos)
    (by rw [mem_ball, dist_eq_norm]; exact hw)
  exact this

/-- a dense sequence in `ℂ` -/
noncomputable def pt (k : ℕ) : ℂ :=
  ⟨((Denumerable.ofNat (ℚ × ℚ) k).1 : ℝ), ((Denumerable.ofNat (ℚ × ℚ) k).2 : ℝ)⟩

lemma pt_dense (z : ℂ) {η : ℝ} (hη : 0 < η) : ∃ k, ‖z - pt k‖ < η := by
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show z.re - η / 3 < z.re + η / 3 by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show z.im - η / 3 < z.im + η / 3 by linarith)
  obtain ⟨k, hk⟩ : ∃ k, Denumerable.ofNat (ℚ × ℚ) k = (a, b) := ⟨_, Denumerable.ofNat_encode (a, b)⟩
  refine ⟨k, ?_⟩
  have hp : pt k = ⟨(a : ℝ), (b : ℝ)⟩ := by
    simp only [pt, hk]
  rw [hp]
  calc ‖z - ⟨(a : ℝ), (b : ℝ)⟩‖ ≤ |(z - ⟨(a : ℝ), (b : ℝ)⟩).re| + |(z - ⟨(a : ℝ), (b : ℝ)⟩).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ < η := by
        simp only [Complex.sub_re, Complex.sub_im]
        have e1 : |z.re - (a : ℝ)| < η / 3 := abs_lt.2 ⟨by linarith, by linarith⟩
        have e2 : |z.im - (b : ℝ)| < η / 3 := abs_lt.2 ⟨by linarith, by linarith⟩
        linarith


theorem montel_main {Ω : Set ℂ} (hΩ : IsRegion Ω)
    {𝔉 : Set (ℂ → ℂ)} (hanal : ∀ f ∈ 𝔉, AnalyticOnNhd ℂ f Ω) :
    IsNormalFamily 𝔉 Ω ↔
      ∀ K ⊆ Ω, IsCompact K → ∃ M : ℝ, ∀ f ∈ 𝔉, ∀ z ∈ K, ‖f z‖ ≤ M := by
  have hΩo : IsOpen Ω := hΩ.1
  constructor
  · intro hN K hK hKc
    by_contra hcon
    push_neg at hcon
    choose F hF z hz hlt using fun n : ℕ => hcon (n : ℝ)
    obtain ⟨φ, hφ, g, hg⟩ := hN F hF
    have hu := hg K hK hKc
    have hcont : ContinuousOn g K := hu.continuousOn (Frequently.of_forall fun n =>
      ((hanal _ (hF (φ n))).continuousOn).mono hK)
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcont
    have h1 := (Metric.tendstoUniformlyOn_iff.1 hu) 1 one_pos
    have h2 : ∀ᶠ n in atTop, C + 1 ≤ (φ n : ℝ) := by
      have : Tendsto (fun n => (φ n : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
      exact this.eventually_ge_atTop _
    obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
    have a1 := hn1 (z (φ n)) (hz (φ n))
    have a2 := hC (z (φ n)) (hz (φ n))
    have a3 := hlt (φ n)
    rw [dist_eq_norm] at a1
    have : ‖F (φ n) (z (φ n))‖ ≤ ‖g (z (φ n))‖ + ‖g (z (φ n)) - F (φ n) (z (φ n))‖ := by
      calc ‖F (φ n) (z (φ n))‖ = ‖g (z (φ n)) - (g (z (φ n)) - F (φ n) (z (φ n)))‖ := by
            congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    linarith
  · intro hbd F hF
    -- bounds at the dense points
    have hB : ∀ k, ∃ B : ℝ, 0 ≤ B ∧ (pt k ∈ Ω → ∀ f ∈ 𝔉, ‖f (pt k)‖ ≤ B) := by
      intro k
      by_cases hk : pt k ∈ Ω
      · obtain ⟨M, hM⟩ := hbd {pt k} (by simpa using hk) isCompact_singleton
        exact ⟨max M 0, le_max_right _ _, fun _ f hf =>
          (hM f hf (pt k) rfl).trans (le_max_left _ _)⟩
      · exact ⟨0, le_rfl, fun h => absurd h hk⟩
    choose B hB0 hBb using hB
    classical
    let x : ℕ → ℕ → ℂ := fun n k => if pt k ∈ Ω then F n (pt k) else 0
    have hxS : ∀ n, x n ∈ Set.pi univ (fun k => closedBall (0 : ℂ) (B k)) := by
      intro n k _
      rw [mem_closedBall_zero_iff]
      simp only [x]
      split_ifs with hk
      · exact hBb k hk _ (hF n)
      · simpa using hB0 k
    obtain ⟨a, -, φ, hφ, hlim⟩ :=
      (isCompact_univ_pi (fun k => isCompact_closedBall (0 : ℂ) (B k))).tendsto_subseq hxS
    have hcoord : ∀ k, CauchySeq (fun n => x (φ n) k) := fun k =>
      ((continuous_apply k).tendsto a |>.comp hlim).cauchySeq
    -- uniform Cauchy on compacts
    have hUC : ∀ K ⊆ Ω, IsCompact K → UniformCauchySeqOn (fun n => F (φ n)) atTop K := by
      intro K hK hKc
      obtain ⟨δ, hδ, L, hL, hLip⟩ := equi hΩo hanal hbd hK hKc
      rw [Metric.uniformCauchySeqOn_iff]
      intro ε hε
      set η := min δ (ε / (3 * (L + 1))) with hη
      have hηpos : 0 < η := lt_min hδ (by positivity)
      obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun k => ball (pt k) η) (fun _ => isOpen_ball)
        (fun z _ => by
          obtain ⟨k, hk⟩ := pt_dense z hηpos
          exact mem_iUnion.2 ⟨k, by rw [mem_ball, dist_eq_norm]; exact hk⟩)
      have hN : ∀ k, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (x (φ m) k) (x (φ n) k) < ε / 3 := fun k =>
        Metric.cauchySeq_iff.1 (hcoord k) _ (by positivity)
      choose N hN using hN
      refine ⟨t.sup N, fun m hm n hn z hz => ?_⟩
      obtain ⟨k, hkt, hzk⟩ := mem_iUnion₂.1 (ht hz)
      rw [mem_ball, dist_eq_norm] at hzk
      have hzk' : ‖pt k - z‖ < δ := by
        rw [norm_sub_rev]; exact hzk.trans_le (min_le_left _ _)
      have hNk : N k ≤ t.sup N := Finset.le_sup hkt
      have hc := hN k m (hNk.trans hm) n (hNk.trans hn)
      have hkΩ : pt k ∈ Ω := (hLip _ (hF 0) z hz _ hzk').1
      simp only [x, hkΩ, if_true] at hc
      rw [dist_eq_norm] at hc ⊢
      have l1 := (hLip _ (hF (φ m)) z hz _ hzk').2
      have l2 := (hLip _ (hF (φ n)) z hz _ hzk').2
      have hLη : L * ‖pt k - z‖ < ε / 3 := by
        have hle : ‖pt k - z‖ < ε / (3 * (L + 1)) := by
          rw [norm_sub_rev]; exact hzk.trans_le (min_le_right _ _)
        calc L * ‖pt k - z‖ ≤ (L + 1) * ‖pt k - z‖ := by nlinarith [norm_nonneg (pt k - z)]
          _ < (L + 1) * (ε / (3 * (L + 1))) := by
              exact mul_lt_mul_of_pos_left hle (by linarith)
          _ = ε / 3 := by field_simp
      calc ‖F (φ m) z - F (φ n) z‖
          = ‖(F (φ m) (pt k) - F (φ n) (pt k)) - (F (φ m) (pt k) - F (φ m) z)
              + (F (φ n) (pt k) - F (φ n) z)‖ := by congr 1; ring
        _ ≤ ‖(F (φ m) (pt k) - F (φ n) (pt k)) - (F (φ m) (pt k) - F (φ m) z)‖
              + ‖F (φ n) (pt k) - F (φ n) z‖ := norm_add_le _ _
        _ ≤ ‖F (φ m) (pt k) - F (φ n) (pt k)‖ + ‖F (φ m) (pt k) - F (φ m) z‖
              + ‖F (φ n) (pt k) - F (φ n) z‖ := by
            linarith [norm_sub_le (F (φ m) (pt k) - F (φ n) (pt k)) (F (φ m) (pt k) - F (φ m) z)]
        _ < ε := by linarith
    refine ⟨φ, hφ, fun z => limUnder atTop (fun n => F (φ n) z), fun K hK hKc => ?_⟩
    refine (hUC K hK hKc).tendstoUniformlyOn_of_tendsto fun z hz => ?_
    have hcs : CauchySeq (fun n => F (φ n) z) := (hUC K hK hKc).cauchySeq hz
    obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcs
    exact tendsto_nhds_limUnder ⟨l, hl⟩

end AhlforsMontel

open AhlforsMontel

theorem solution {Ω : Set ℂ} (hΩ : IsRegion Ω)
    {𝔉 : Set (ℂ → ℂ)} (hanal : ∀ f ∈ 𝔉, AnalyticOnNhd ℂ f Ω) :
    IsNormalFamily 𝔉 Ω ↔
      ∀ K ⊆ Ω, IsCompact K → ∃ M : ℝ, ∀ f ∈ 𝔉, ∀ z ∈ K, ‖f z‖ ≤ M := by
  exact AhlforsMontel.montel_main hΩ hanal
