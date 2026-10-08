-- Prove2me | solution 1 for AhlforsComplexAnalysis.rmt_exists_extremal
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T12:35:28.622525+00:00
-- url     : https://prove2.me/submissions/7326472d-77a2-45fd-9043-da9eb895647e

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Defs
import Theorems.Thm_AhlforsComplexAnalysis_hurwitz
import Theorems.Thm_AhlforsComplexAnalysis_normal_iff_locally_bounded

set_option autoImplicit false

open AhlforsComplexAnalysis

namespace AhlforsExtremal

/-- Injective analytic maps of `Ω` into the open unit disc sending `z₀` to `0`. -/
def rmtE_F (Ω : Set ℂ) (z₀ : ℂ) : Set (ℂ → ℂ) :=
  {h | AnalyticOnNhd ℂ h Ω ∧ (∀ z ∈ Ω, ‖h z‖ < 1) ∧ h z₀ = 0 ∧ Set.InjOn h Ω}

lemma rmtE_isPreconnected_punctured_ball (z₁ : ℂ) {ε : ℝ} (hε : 0 < ε) :
    IsPreconnected (Metric.ball z₁ ε \ {z₁}) := by
  have hconn : IsConnected ({0}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 0
  set g : ℂ → ℂ := fun w => z₁ + ((ε / (1 + ‖w‖) : ℝ) : ℂ) * w with hg
  have hcont : Continuous g := by
    have h1 : Continuous (fun w : ℂ => ε / (1 + ‖w‖)) :=
      continuous_const.div (by fun_prop) (fun w => by positivity)
    rw [hg]
    fun_prop
  have himg : g '' {0}ᶜ = Metric.ball z₁ ε \ {z₁} := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
      have hc : 0 < ε / (1 + ‖w‖) := by positivity
      refine ⟨?_, ?_⟩
      · rw [mem_ball_iff_norm]
        have : g w - z₁ = ((ε / (1 + ‖w‖) : ℝ) : ℂ) * w := by simp [hg]
        rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc,
          div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      · intro h
        have h' : ((ε / (1 + ‖w‖) : ℝ) : ℂ) * w = 0 := by
          have : g w = z₁ := h
          simpa [hg] using this
        rcases mul_eq_zero.mp h' with h0 | h0
        · exact hc.ne' (by exact_mod_cast h0)
        · exact hw h0
    · rintro ⟨hy, hy1⟩
      have hy1' : y - z₁ ≠ 0 := sub_ne_zero.mpr hy1
      set t : ℝ := ‖y - z₁‖ with ht
      have ht0 : 0 < t := norm_pos_iff.mpr hy1'
      have htε : t < ε := by rwa [mem_ball_iff_norm] at hy
      have hεt : 0 < ε - t := by linarith
      refine ⟨(y - z₁) / ((ε - t : ℝ) : ℂ), ?_, ?_⟩
      · have : ((ε - t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hεt.ne'
        exact div_ne_zero hy1' this
      · have hn : ‖(y - z₁) / ((ε - t : ℝ) : ℂ)‖ = t / (ε - t) := by
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hεt]
        have h2 : ε / (1 + t / (ε - t)) = ε - t := by
          field_simp
          ring
        simp only [hg, hn, h2]
        have : ((ε - t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hεt.ne'
        field_simp
        ring
  rw [← himg]
  exact (hconn.image g hcont.continuousOn).isPreconnected

lemma rmtE_isRegion_diff_singleton {Ω : Set ℂ} (hΩ : IsRegion Ω) {z₁ : ℂ} (hz₁ : z₁ ∈ Ω) :
    IsRegion (Ω \ {z₁}) := by
  obtain ⟨hopen, hconn⟩ := hΩ
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen z₁ hz₁
  have hD := rmtE_isPreconnected_punctured_ball z₁ hε
  have hDU : Metric.ball z₁ ε \ {z₁} ⊆ Ω \ {z₁} := fun x hx => ⟨hball hx.1, hx.2⟩
  refine ⟨hopen.sdiff isClosed_singleton, ?_, ?_⟩
  · refine ⟨z₁ + ((ε / 2 : ℝ) : ℂ), hball ?_, ?_⟩
    · rw [mem_ball_iff_norm]
      simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
      linarith
    · intro h
      have : ((ε / 2 : ℝ) : ℂ) = 0 := by simpa using h
      have : ε / 2 = 0 := by exact_mod_cast this
      linarith
  · intro u v hu hv hUuv ⟨a, haU, hau⟩ ⟨b, hbU, hbv⟩
    by_contra hcon
    have hempty : ∀ x ∈ Ω \ {z₁}, x ∈ u → x ∈ v → False :=
      fun x hx hxu hxv => hcon ⟨x, hx, hxu, hxv⟩
    -- inner claim: if the punctured ball lies in `u` we contradict preconnectedness of `Ω`
    have inner : ∀ u v : Set ℂ, IsOpen u → IsOpen v → Ω \ {z₁} ⊆ u ∪ v →
        (∀ x ∈ Ω \ {z₁}, x ∈ u → x ∈ v → False) → ∀ b ∈ Ω \ {z₁}, b ∈ v →
        Metric.ball z₁ ε \ {z₁} ⊆ u → False := by
      intro u v hu hv hUuv hempty b hbU hbv hDu
      have hu' : IsOpen (u ∪ Metric.ball z₁ ε) := hu.union Metric.isOpen_ball
      have hv' : IsOpen (v \ {z₁}) := hv.sdiff isClosed_singleton
      have hcov : Ω ⊆ (u ∪ Metric.ball z₁ ε) ∪ (v \ {z₁}) := by
        intro x hx
        by_cases hxz : x = z₁
        · subst hxz
          exact Or.inl (Or.inr (Metric.mem_ball_self hε))
        · rcases hUuv ⟨hx, hxz⟩ with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr ⟨h, hxz⟩
      obtain ⟨x, hxΩ, hxu, hxv⟩ := hconn.2 _ _ hu' hv' hcov
        ⟨z₁, hz₁, Or.inr (Metric.mem_ball_self hε)⟩ ⟨b, hbU.1, hbv, hbU.2⟩
      have hxz : x ≠ z₁ := hxv.2
      rcases hxu with h | h
      · exact hempty x ⟨hxΩ, hxz⟩ h hxv.1
      · exact hempty x ⟨hxΩ, hxz⟩ (hDu ⟨h, hxz⟩) hxv.1
    have hDcov : Metric.ball z₁ ε \ {z₁} ⊆ u ∪ v := fun x hx => hUuv (hDU hx)
    by_cases h1 : ((Metric.ball z₁ ε \ {z₁}) ∩ v).Nonempty
    · by_cases h2 : ((Metric.ball z₁ ε \ {z₁}) ∩ u).Nonempty
      · obtain ⟨x, hx, hxu, hxv⟩ := hD u v hu hv hDcov h2 h1
        exact hempty x (hDU hx) hxu hxv
      · refine inner v u hv hu (by rwa [Set.union_comm]) (fun x hx h h' => hempty x hx h' h)
          a haU hau ?_
        intro x hx
        rcases hDcov hx with h | h
        · exact absurd ⟨x, hx, h⟩ h2
        · exact h
    · exact inner u v hu hv hUuv hempty b hbU hbv (by
        intro x hx
        rcases hDcov hx with h | h
        · exact h
        · exact absurd ⟨x, hx, h⟩ h1)


lemma rmtE_deriv_eq_zero_of_eqOn_const {Ω : Set ℂ} (hopen : IsOpen Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    {f : ℂ → ℂ} {c : ℂ} (h : ∀ z ∈ Ω, f z = c) : deriv f z₀ = 0 := by
  have : f =ᶠ[nhds z₀] fun _ => c := by
    filter_upwards [hopen.mem_nhds hz₀] with z hz using h z hz
  rw [this.deriv_eq]
  simp

lemma rmtE_deriv_bound {Ω : Set ℂ} (hopen : IsOpen Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ B : ℝ, ∀ h ∈ rmtE_F Ω z₀, ‖deriv h z₀‖ ≤ B := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen z₀ hz₀
  refine ⟨1 / (ε / 2), fun h hh => ?_⟩
  have hsub : Metric.closedBall z₀ (ε / 2) ⊆ Ω :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hd : DiffContOnCl ℂ h (Metric.ball z₀ (ε / 2)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ (by positivity)]
    exact fun z hz => (hh.1 z (hsub hz)).differentiableAt.differentiableWithinAt
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) hd
    (fun z hz => (hh.2.1 z (hsub (Metric.sphere_subset_closedBall hz))).le)

lemma rmtE_exists_mem_deriv_ne_zero {Ω : Set ℂ} (hΩ : IsRegion Ω) (hne : Ω ≠ Set.univ)
    (hroot : ∀ u : ℂ → ℂ, AnalyticOnNhd ℂ u Ω → (∀ z ∈ Ω, u z ≠ 0) →
      ∃ r : ℂ → ℂ, AnalyticOnNhd ℂ r Ω ∧ ∀ z ∈ Ω, r z ^ 2 = u z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ h ∈ rmtE_F Ω z₀, deriv h z₀ ≠ 0 := by
  obtain ⟨a, ha⟩ : ∃ a, a ∉ Ω := by
    by_contra hcon
    exact hne (Set.eq_univ_of_forall fun a => not_not.mp fun h => hcon ⟨a, h⟩)
  obtain ⟨g, hgan, hg2⟩ := hroot (fun z => z - a) (analyticOnNhd_id.sub analyticOnNhd_const)
    (fun z hz => sub_ne_zero.mpr (fun h => ha (h ▸ hz)))
  have hginj : Set.InjOn g Ω := by
    intro z₁ h₁ z₂ h₂ h
    have : z₁ - a = z₂ - a := by rw [← hg2 z₁ h₁, ← hg2 z₂ h₂, h]
    linear_combination this
  have hgneg : ∀ z₁ ∈ Ω, ∀ z₂ ∈ Ω, g z₁ ≠ - g z₂ := by
    intro z₁ h₁ z₂ h₂ h
    have hsq : z₁ - a = z₂ - a := by rw [← hg2 z₁ h₁, ← hg2 z₂ h₂, h]; ring
    have hz : z₁ = z₂ := by linear_combination hsq
    subst hz
    have h0 : g z₁ = 0 := by linear_combination h / 2
    have h3 : z₁ - a = 0 := by rw [← hg2 z₁ h₁, h0]; ring
    exact ha (by rw [← sub_eq_zero.mp h3]; exact h₁)
  have hdiff : HasDerivAt g (deriv g z₀) z₀ := (hgan z₀ hz₀).differentiableAt.hasDerivAt
  have hgd : deriv g z₀ ≠ 0 := by
    have h1 : HasDerivAt (fun z => g z * g z) (deriv g z₀ * g z₀ + g z₀ * deriv g z₀) z₀ :=
      hdiff.mul hdiff
    have h2 : HasDerivAt (fun z => g z * g z) 1 z₀ := by
      have : HasDerivAt (fun z : ℂ => z - a) 1 z₀ := (hasDerivAt_id z₀).sub_const a
      refine this.congr_of_eventuallyEq ?_
      filter_upwards [hΩ.1.mem_nhds hz₀] with z hz using (by rw [← sq]; exact hg2 z hz)
    have h3 := h1.unique h2
    intro h0
    rw [h0] at h3
    simp at h3
  have hopen : IsOpen (g '' Ω) := by
    rcases hgan.is_constant_or_isOpen hΩ.2.isPreconnected with ⟨w, hw⟩ | h
    · exfalso
      exact hgd (rmtE_deriv_eq_zero_of_eqOn_const hΩ.1 hz₀ hw)
    · exact h Ω subset_rfl hΩ.1
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen (g z₀) ⟨z₀, hz₀, rfl⟩
  have hlow : ∀ z ∈ Ω, r ≤ ‖g z + g z₀‖ := by
    intro z hz
    by_contra hlt
    have hlt := not_le.mp hlt
    have hmem : -g z ∈ Metric.ball (g z₀) r := by
      rw [mem_ball_iff_norm]
      have : -g z - g z₀ = -(g z + g z₀) := by ring
      rw [this, norm_neg]
      exact hlt
    obtain ⟨z', hz', hz'eq⟩ := hball hmem
    exact hgneg z' hz' z hz hz'eq
  have hden : ∀ z ∈ Ω, g z + g z₀ ≠ 0 := fun z hz h => by
    have := hlow z hz
    rw [h, norm_zero] at this
    linarith
  have hr4 : (0 : ℝ) < r / 4 := by positivity
  have hr' : ((r / 4 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr4.ne'
  set h₁ : ℂ → ℂ := fun z => ((r / 4 : ℝ) : ℂ) / (g z + g z₀) with hh₁
  have hb : ∀ w ∈ Ω, ‖h₁ w‖ ≤ 1 / 4 := by
    intro w hw
    have hlw := hlow w hw
    show ‖((r / 4 : ℝ) : ℂ) / (g w + g z₀)‖ ≤ 1 / 4
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr4,
      div_le_iff₀ (lt_of_lt_of_le hr hlw)]
    linarith
  refine ⟨fun z => h₁ z - h₁ z₀, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro z hz
    have : AnalyticAt ℂ h₁ z :=
      analyticAt_const.div ((hgan z hz).add analyticAt_const) (hden z hz)
    exact this.sub analyticAt_const
  · intro z hz
    calc ‖h₁ z - h₁ z₀‖ ≤ ‖h₁ z‖ + ‖h₁ z₀‖ := norm_sub_le _ _
      _ ≤ 1 / 4 + 1 / 4 := add_le_add (hb z hz) (hb z₀ hz₀)
      _ < 1 := by norm_num
  · simp
  · intro z₁ h₁' z₂ h₂' hEq
    have h12 : h₁ z₁ = h₁ z₂ := sub_left_inj.mp hEq
    apply hginj h₁' h₂'
    have hz₁ := hden z₁ h₁'
    have hz₂ := hden z₂ h₂'
    have h13 : g z₁ + g z₀ = g z₂ + g z₀ := by
      simp only [hh₁] at h12
      rw [div_eq_div_iff hz₁ hz₂] at h12
      exact (mul_left_cancel₀ hr' h12).symm
    linear_combination h13
  · have hd : HasDerivAt (fun z => h₁ z - h₁ z₀)
        ((0 * (g z₀ + g z₀) - ((r / 4 : ℝ) : ℂ) * deriv g z₀) / (g z₀ + g z₀) ^ 2) z₀ :=
      ((hasDerivAt_const z₀ (((r / 4 : ℝ) : ℂ))).div
        (hdiff.add_const (g z₀)) (hden z₀ hz₀)).sub_const (h₁ z₀)
    rw [hd.deriv]
    refine div_ne_zero ?_ (pow_ne_zero 2 (hden z₀ hz₀))
    simp [hgd, hr.ne']

lemma rmtE_limit {Ω : Set ℂ} (hΩ : IsRegion Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (h : ℕ → ℂ → ℂ) (hh : ∀ n, h n ∈ rmtE_F Ω z₀) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f Ω ∧
      (∀ K ⊆ Ω, IsCompact K → TendstoUniformlyOn (fun n => h (φ n)) f Filter.atTop K) ∧
      Filter.Tendsto (fun n => deriv (h (φ n)) z₀) Filter.atTop (nhds (deriv f z₀)) := by
  have hnormal : IsNormalFamily (rmtE_F Ω z₀) Ω := by
    rw [normal_iff_locally_bounded hΩ (fun f hf => hf.1)]
    exact fun K hKΩ _ => ⟨1, fun f hf z hz => (hf.2.1 z (hKΩ hz)).le⟩
  obtain ⟨φ, hφ, f, hf⟩ := hnormal h hh
  have hlu : TendstoLocallyUniformlyOn (fun n => h (φ n)) f Filter.atTop Ω :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ.1).mpr hf
  have hdiff : ∀ᶠ n in Filter.atTop, DifferentiableOn ℂ (fun z => h (φ n) z) Ω :=
    Filter.Eventually.of_forall fun n => (hh (φ n)).1.differentiableOn
  have hfd : DifferentiableOn ℂ f Ω := hlu.differentiableOn hdiff hΩ.1
  refine ⟨φ, hφ, f, hfd.analyticOnNhd hΩ.1, hf, ?_⟩
  exact (hlu.deriv hdiff hΩ.1).tendsto_at hz₀

lemma rmtE_tendstoUniformlyOn_sub_const {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {K : Set ℂ} {z₁ : ℂ}
    (h : TendstoUniformlyOn F f Filter.atTop (insert z₁ K)) :
    TendstoUniformlyOn (fun n z => F n z - F n z₁) (fun z => f z - f z₁) Filter.atTop K := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h (ε / 2) (half_pos hε)] with n hn z hz
  have h1 := hn z (Set.mem_insert_of_mem _ hz)
  have h2 := hn z₁ (Set.mem_insert _ _)
  calc dist (f z - f z₁) (F n z - F n z₁) ≤ dist (f z) (F n z) + dist (f z₁) (F n z₁) :=
        dist_sub_sub_le _ _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := by ring

end AhlforsExtremal

open AhlforsExtremal

theorem solution {Ω : Set ℂ} (hΩ : IsRegion Ω) (hne : Ω ≠ Set.univ)
    (hroot : ∀ u : ℂ → ℂ, AnalyticOnNhd ℂ u Ω → (∀ z ∈ Ω, u z ≠ 0) →
      ∃ r : ℂ → ℂ, AnalyticOnNhd ℂ r Ω ∧ ∀ z ∈ Ω, r z ^ 2 = u z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f Ω ∧ (∀ z ∈ Ω, ‖f z‖ < 1) ∧ f z₀ = 0 ∧ Set.InjOn f Ω ∧
      deriv f z₀ ≠ 0 ∧
      ∀ h : ℂ → ℂ, AnalyticOnNhd ℂ h Ω → (∀ z ∈ Ω, ‖h z‖ < 1) → h z₀ = 0 → Set.InjOn h Ω →
        ‖deriv h z₀‖ ≤ ‖deriv f z₀‖ := by
  obtain ⟨h₀, hh₀, hh₀d⟩ := rmtE_exists_mem_deriv_ne_zero hΩ hne hroot hz₀
  obtain ⟨B, hB⟩ := rmtE_deriv_bound hΩ.1 hz₀
  set S : Set ℝ := (fun h : ℂ → ℂ => ‖deriv h z₀‖) '' rmtE_F Ω z₀ with hS
  have hSne : S.Nonempty := ⟨_, h₀, hh₀, rfl⟩
  have hSbdd : BddAbove S := ⟨B, by rintro _ ⟨h, hh, rfl⟩; exact hB h hh⟩
  set M := sSup S with hM
  have hle : ∀ h ∈ rmtE_F Ω z₀, ‖deriv h z₀‖ ≤ M := fun h hh => le_csSup hSbdd ⟨h, hh, rfl⟩
  have hMpos : 0 < M := lt_of_lt_of_le (norm_pos_iff.mpr hh₀d) (hle h₀ hh₀)
  have hseq : ∀ n : ℕ, ∃ h ∈ rmtE_F Ω z₀, M - 1 / ((n : ℝ) + 1) < ‖deriv h z₀‖ := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨_, ⟨h, hh, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hSne (show M - 1 / ((n : ℝ) + 1) < M by linarith)
    exact ⟨h, hh, hlt⟩
  choose hs hsF hsgt using hseq
  obtain ⟨φ, hφ, f, hfan, hfconv, hfd⟩ := rmtE_limit hΩ hz₀ hs hsF
  have hnormT : Filter.Tendsto (fun n => ‖deriv (hs (φ n)) z₀‖) Filter.atTop (nhds M) := by
    have h1 : Filter.Tendsto (fun n : ℕ => ‖deriv (hs n) z₀‖) Filter.atTop (nhds M) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le
        (g := fun n : ℕ => M - 1 / ((n : ℝ) + 1)) (h := fun _ => M) ?_ tendsto_const_nhds
        (fun n => (hsgt n).le) (fun n => hle _ (hsF n))
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using (tendsto_const_nhds (x := M)).sub this
    exact h1.comp hφ.tendsto_atTop
  have hfM : ‖deriv f z₀‖ = M := tendsto_nhds_unique hfd.norm hnormT
  have hfz₀ : f z₀ = 0 := by
    have := (hfconv {z₀} (by simpa using hz₀) isCompact_singleton).tendsto_at
      (Set.mem_singleton z₀)
    refine tendsto_nhds_unique this ?_
    simp only [(hsF _).2.2.1]
    exact tendsto_const_nhds
  have hfle : ∀ z ∈ Ω, ‖f z‖ ≤ 1 := by
    intro z hz
    have := (hfconv {z} (by simpa using hz) isCompact_singleton).tendsto_at
      (Set.mem_singleton z)
    exact le_of_tendsto this.norm
      (Filter.Eventually.of_forall fun n => ((hsF (φ n)).2.1 z hz).le)
  have hfd0 : deriv f z₀ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hfM
    linarith
  have hnoconst : ∀ c : ℂ, ¬ ∀ z ∈ Ω, f z = c :=
    fun c hc => hfd0 (rmtE_deriv_eq_zero_of_eqOn_const hΩ.1 hz₀ hc)
  have hflt : ∀ z ∈ Ω, ‖f z‖ < 1 := by
    intro z hz
    refine lt_of_le_of_ne (hfle z hz) ?_
    intro h1
    apply hnoconst (f z)
    have hmax : IsMaxOn (norm ∘ f) Ω z := fun w hw => by
      simp only [Function.comp]
      rw [h1]
      exact hfle w hw
    exact fun w hw => Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hΩ.2.isPreconnected hΩ.1
      hfan.differentiableOn hz hmax hw
  have hfinj : Set.InjOn f Ω := by
    intro z₁ hz₁ z₂ hz₂ heq
    by_contra hne12
    have hU := rmtE_isRegion_diff_singleton hΩ hz₁
    have hcases := AhlforsComplexAnalysis.hurwitz hU
      (F := fun n z => hs (φ n) z - hs (φ n) z₁) (f := fun z => f z - f z₁)
      (fun n => ((hsF (φ n)).1.mono Set.sdiff_subset).sub analyticOnNhd_const)
      (fun n z hz hz0 => hz.2 ((hsF (φ n)).2.2.2 hz.1 hz₁ (sub_eq_zero.mp hz0)))
      (fun K hKU hK => rmtE_tendstoUniformlyOn_sub_const
        (hfconv (insert z₁ K) (Set.insert_subset hz₁ (hKU.trans Set.sdiff_subset))
          (hK.insert z₁)))
    rcases hcases with h | h
    · apply hnoconst (f z₁)
      intro z hz
      by_cases hzz : z = z₁
      · rw [hzz]
      · exact sub_eq_zero.mp (h z ⟨hz, hzz⟩)
    · have hz₂' : z₂ ≠ z₁ := fun h' => hne12 h'.symm
      exact h z₂ ⟨hz₂, hz₂'⟩ (sub_eq_zero.mpr heq.symm)
  exact ⟨f, hfan, hflt, hfz₀, hfinj, hfd0,
    fun h hh1 hh2 hh3 hh4 => hfM ▸ hle h ⟨hh1, hh2, hh3, hh4⟩⟩

#print axioms solution
