-- Prove2me | solution 1 for AffineStorage.Ruin.proposition_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T00:12:52.690504+00:00
-- url     : https://prove2.me/submissions/47502ebe-f260-4911-b158-0553e8f7674c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AffineStorage_Ruin_Model
import Theorems.Thm_AffineStorage_Ruin_eq_2
import Theorems.Thm_AffineStorage_Ruin_lemma_1
import Theorems.Thm_AffineStorage_Ruin_drift_transforms
import Theorems.Thm_AffineStorage_Ruin_convolution_transform
import Theorems.Thm_AffineStorage_Ruin_ruin_term_transform
import Theorems.Thm_AffineStorage_Ruin_eq_5
open MeasureTheory ProbabilityTheory Filter Topology
open AffineStorage.Ruin

/-- Pathwise: on the good event of `eq_2`, the penalty at a finite ruin time is in `[0,1]`. -/
lemma affRuin_payoff_le_one (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (x : ℝ) (hx : 0 < x) (ω : Ω)
    (hX0 : B.X P x 0 ω = x)
    (hrc : ∀ t, ContinuousWithinAt (fun s => B.X P x s ω) (Set.Ici t) t)
    (hll : ∀ t, Tendsto (fun s => B.X P x s ω) (𝓝[<] t) (𝓝 (B.Xminus P x t ω)))
    (hτ : B.tau P x ω < ⊤) : B.payoff P x ω ≤ 1 := by
  obtain ⟨-, -, -, -, -, -, hα, hβ, hγ, -⟩ := hS
  set f : ℝ → ℝ := fun s => B.X P x s ω with hf
  set t := (B.tau P x ω).toReal with ht_def
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have hτt : B.tau P x ω = ENNReal.ofReal t := (ENNReal.ofReal_toReal hτ.ne).symm
  have ha : ∀ s, 0 < s → f s ≤ 0 → t ≤ s := by
    intro s hs hfs
    refine ENNReal.toReal_le_of_le_ofReal hs.le ?_
    unfold Basis.tau
    exact iInf₂_le s ⟨hs, hfs⟩
  have hb : f t ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have hev : ∀ᶠ s in 𝓝[≥] t, 0 < f s := (hrc t).eventually (lt_mem_nhds hcon)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hev
    have hu' : t < u := hu
    have hle : ENNReal.ofReal u ≤ B.tau P x ω := by
      unfold Basis.tau
      refine le_iInf₂ fun s hs => ENNReal.ofReal_le_ofReal ?_
      have hts := ha s hs.1 hs.2
      by_contra hsu
      push Not at hsu
      have := hsub ⟨hts, hsu⟩
      simp only [Set.mem_setOf_eq] at this
      exact absurd hs.2 (not_le.mpr this)
    rw [hτt] at hle
    have := (ENNReal.ofReal_le_ofReal_iff ht0).mp hle
    linarith
  have htpos : 0 < t := by
    rcases ht0.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hb; simp only [hf] at hb; rw [hX0] at hb; linarith
  have hd : 0 ≤ B.Xminus P x t ω := by
    refine ge_of_tendsto (hll t) ?_
    filter_upwards [Ioo_mem_nhdsLT htpos] with s hs
    by_contra hcon
    push Not at hcon
    have := ha s hs.1 hcon.le
    linarith [hs.2]
  unfold Basis.payoff
  rw [Real.exp_le_one_iff]
  have h1 : 0 ≤ P.α * t := mul_nonneg hα ht0
  have h2 : P.β * B.X P x t ω ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ hb
  have h3 : 0 ≤ P.γ * B.Xminus P x t ω := mul_nonneg hγ hd
  rw [← ht_def]
  linarith

lemma affRuin_rho_abs_le_one (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (hB : B.IsValid P) (x : ℝ) (hx : 0 < x) : |rho B P x| ≤ 1 := by
  have hν : 0 < P.ν := hS.2.2.2.2.2.1
  have := isProbabilityMeasure_expMeasure hν
  have : IsProbabilityMeasure B.P := hB.1
  obtain ⟨-, hgood⟩ := eq_2 P hS B hB x
  have hinner : ∀ s : ℝ, ‖∫ ω, Set.indicator {ω | B.tau P x ω < ENNReal.ofReal s}
      (B.payoff P x) ω ∂B.P‖ ≤ 1 := by
    intro s
    have := norm_integral_le_of_norm_le (integrable_const (1 : ℝ)) (μ := B.P)
      (f := Set.indicator {ω | B.tau P x ω < ENNReal.ofReal s} (B.payoff P x)) ?_
    · simpa using this
    filter_upwards [hgood] with ω hω
    obtain ⟨h0, hrc, hll, -, -⟩ := hω
    by_cases hm : ω ∈ {ω | B.tau P x ω < ENNReal.ofReal s}
    · rw [Set.indicator_of_mem hm, Real.norm_eq_abs,
        abs_of_nonneg (by unfold Basis.payoff; exact (Real.exp_pos _).le)]
      exact affRuin_payoff_le_one P hS B x hx ω h0 hrc hll
        (lt_of_lt_of_le hm le_top)
    · rw [Set.indicator_of_notMem hm]; simp
  have := norm_integral_le_of_norm_le (integrable_const (1 : ℝ)) (μ := expMeasure P.ν)
    (ae_of_all _ hinner)
  simpa [rho] using this

lemma affRuin_phi_abs_le_one (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (hB : B.IsValid P) (ϑ : ℝ) (hϑ : 0 < ϑ) : |phi B P ϑ| ≤ 1 := by
  have hint : IntegrableOn (fun x => ϑ * Real.exp (-(ϑ * x))) (Set.Ioi 0) := by
    have := (exp_neg_integrableOn_Ioi 0 hϑ).const_mul ϑ
    simp only [neg_mul] at this; exact this
  have hval : ∫ x in Set.Ioi (0 : ℝ), ϑ * Real.exp (-(ϑ * x)) = 1 := by
    rw [integral_const_mul]
    have := integral_exp_mul_Ioi (a := -ϑ) (by linarith) 0
    simp only [mul_zero, Real.exp_zero, neg_mul] at this
    rw [this]; field_simp
  have := norm_integral_le_of_norm_le hint (μ := volume.restrict (Set.Ioi 0))
    (f := fun x => ϑ * Real.exp (-(ϑ * x)) * rho B P x) ?_
  · rw [hval] at this; simpa [phi] using this
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_)
  have hr := affRuin_rho_abs_le_one P hS B hB x hx
  have hp : 0 < ϑ * Real.exp (-(ϑ * x)) := mul_pos hϑ (Real.exp_pos _)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp]
  nlinarith [abs_nonneg (rho B P x)]
/-- `∫_a^b g = J(a) - J(b)` for `0 ≤ a ≤ b`, where `J(a) = ∫_{(a,∞)} g`. -/
lemma affRuin_interval_eq_sub {g : ℝ → ℝ} (hg : IntegrableOn g (Set.Ioi 0)) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ x in a..b, g x = (∫ x in Set.Ioi a, g x) - ∫ x in Set.Ioi b, g x := by
  rw [intervalIntegral.integral_of_le hab, ← Set.Ioc_union_Ioi_eq_Ioi hab,
    setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hg.mono_set fun x hx => lt_of_le_of_lt ha hx.1)
      (hg.mono_set fun x hx => lt_of_le_of_lt (ha.trans hab) hx)]
  ring

/-- `a ↦ ∫_{(a,∞)} g` is continuous on `[0, ∞)`. -/
lemma affRuin_J_continuousOn {g : ℝ → ℝ} (hg : IntegrableOn g (Set.Ioi 0)) :
    ContinuousOn (fun a => ∫ x in Set.Ioi a, g x) (Set.Ici 0) := by
  intro c hc
  have hc0 : (0 : ℝ) ≤ c := hc
  have hii : IntervalIntegrable g volume 0 (c + 1) := by
    refine (IntegrableOn.intervalIntegrable ?_)
    rw [Set.uIcc_of_le (by linarith)]
    exact (integrableOn_Icc_iff_integrableOn_Ioc).mpr
      (hg.mono_set fun x hx => hx.1)
  have hcont := intervalIntegral.continuousOn_primitive_interval' hii
    (Set.left_mem_uIcc)
  rw [Set.uIcc_of_le (by linarith)] at hcont
  have heq : Set.EqOn (fun a => ∫ x in Set.Ioi a, g x)
      (fun a => (∫ x in Set.Ioi 0, g x) - ∫ x in (0:ℝ)..a, g x) (Set.Icc 0 (c + 1)) := by
    intro a ha
    simp only
    rw [affRuin_interval_eq_sub hg le_rfl ha.1]; ring
  have h1 : ContinuousWithinAt (fun a => ∫ x in Set.Ioi a, g x) (Set.Icc 0 (c + 1)) c :=
    ((continuousOn_const.sub hcont).congr heq) c ⟨hc0, by linarith⟩
  refine h1.mono_of_mem_nhdsWithin ?_
  rw [← Set.Ici_inter_Iic]
  exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))

lemma affRuin_J_tendsto_right {g : ℝ → ℝ} (hg : IntegrableOn g (Set.Ioi 0)) {c : ℝ}
    (hc : 0 ≤ c) :
    Tendsto (fun a => ∫ x in Set.Ioi a, g x) (𝓝[>] c) (𝓝 (∫ x in Set.Ioi c, g x)) :=
  ((affRuin_J_continuousOn hg) c hc).tendsto.mono_left
    (nhdsWithin_mono _ fun x hx => le_of_lt (lt_of_le_of_lt hc hx))

lemma affRuin_J_tendsto_left {g : ℝ → ℝ} (hg : IntegrableOn g (Set.Ioi 0)) {c : ℝ}
    (hc : 0 < c) :
    Tendsto (fun a => ∫ x in Set.Ioi a, g x) (𝓝[<] c) (𝓝 (∫ x in Set.Ioi c, g x)) :=
  ((affRuin_J_continuousOn hg) c hc.le).tendsto.mono_left
    (nhdsWithin_le_of_mem (mem_of_superset (Ioo_mem_nhdsLT hc) fun x hx => le_of_lt hx.1))

lemma affRuin_J_tendsto_atTop {g : ℝ → ℝ} (hg : IntegrableOn g (Set.Ioi 0)) :
    Tendsto (fun a => ∫ x in Set.Ioi a, g x) atTop (𝓝 0) := by
  have h := intervalIntegral_tendsto_integral_Ioi 0 hg tendsto_id
  have h2 : Tendsto (fun a => (∫ x in Set.Ioi 0, g x) - ∫ x in (0:ℝ)..id a, g x) atTop
      (𝓝 ((∫ x in Set.Ioi 0, g x) - ∫ x in Set.Ioi 0, g x)) := tendsto_const_nhds.sub h
  rw [sub_self] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with a ha
  simp only [id]
  rw [affRuin_interval_eq_sub hg le_rfl ha]; ring

lemma affRuin_psi_tendsto {φ Fs : ℝ → ℝ} (hb : ∀ ϑ, 0 < ϑ → |φ ϑ| ≤ 1) {l : Filter ℝ}
    (hpos : ∀ᶠ ϑ in l, 0 < ϑ) (hF : Tendsto Fs l atTop) :
    Tendsto (fun ϑ => φ ϑ * Real.exp (-(Fs ϑ))) l (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (Real.tendsto_exp_neg_atTop_nhds_zero.comp hF)
  filter_upwards [hpos] with ϑ hϑ
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  simp only [Function.comp]
  nlinarith [hb ϑ hϑ, Real.exp_pos (-(Fs ϑ))]

/-- The ODE-solving core: `ψ = φ e^{-F⋆}` has derivative `g` off `{μ}`, `φ` is bounded and
`F⋆ → ∞` at `0⁺, μ^±, ∞`. Then `ψ = -J` on `(0,μ) ∪ (μ,∞)` and `J(0) = J(μ) = 0`. -/
lemma affRuin_core {φ Fs g : ℝ → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hd : ∀ ϑ, 0 < ϑ → ϑ ≠ μ → HasDerivAt (fun t => φ t * Real.exp (-(Fs t))) (g ϑ) ϑ)
    (hg : IntegrableOn g (Set.Ioi 0)) (hb : ∀ ϑ, 0 < ϑ → |φ ϑ| ≤ 1)
    (hF1 : Tendsto Fs atTop atTop) (hF2 : Tendsto Fs (𝓝[>] 0) atTop)
    (hF3 : Tendsto Fs (𝓝[<] μ) atTop) (hF4 : Tendsto Fs (𝓝[>] μ) atTop) :
    (∀ ϑ, 0 < ϑ → ϑ ≠ μ → φ ϑ * Real.exp (-(Fs ϑ)) = -∫ x in Set.Ioi ϑ, g x) ∧
    (∫ x in Set.Ioi μ, g x) = 0 ∧ (∫ x in Set.Ioi 0, g x) = 0 := by
  set ψ := fun t => φ t * Real.exp (-(Fs t)) with hψ
  set J := fun a => ∫ x in Set.Ioi a, g x with hJ
  -- FTC on an interval avoiding `0` and `μ`
  have ftc : ∀ a b, 0 < a → a ≤ b → (∀ x ∈ Set.Icc a b, x ≠ μ) → ψ b - ψ a = J a - J b := by
    intro a b ha hab hμab
    have hii : IntervalIntegrable g volume a b := by
      refine IntegrableOn.intervalIntegrable (hg.mono_set ?_)
      rw [Set.uIcc_of_le hab]; exact fun x hx => lt_of_lt_of_le ha hx.1
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (f := ψ) (fun x hx => ?_) hii]
    · exact affRuin_interval_eq_sub hg ha.le hab
    · rw [Set.uIcc_of_le hab] at hx
      exact hd x (lt_of_lt_of_le ha hx.1) (hμab x hx)
  -- upper component
  have hup : ∀ a, μ < a → ψ a = -J a := by
    intro a ha
    have hlim1 : Tendsto (fun b => ψ b - ψ a) atTop (𝓝 (0 - ψ a)) :=
      (affRuin_psi_tendsto hb (eventually_gt_atTop 0) hF1).sub tendsto_const_nhds
    have hlim2 : Tendsto (fun b => J a - J b) atTop (𝓝 (J a - 0)) :=
      tendsto_const_nhds.sub (affRuin_J_tendsto_atTop hg)
    have hev : (fun b => ψ b - ψ a) =ᶠ[atTop] (fun b => J a - J b) := by
      filter_upwards [eventually_ge_atTop a] with b hb'
      exact ftc a b (by linarith) hb' fun x hx => by linarith [hx.1]
    have := tendsto_nhds_unique (hlim1.congr' hev) hlim2
    linarith
  have hJμ : J μ = 0 := by
    have h1 : Tendsto J (𝓝[>] μ) (𝓝 (J μ)) := affRuin_J_tendsto_right hg hμ.le
    have h2 : Tendsto (fun a => -ψ a) (𝓝[>] μ) (𝓝 (-0)) :=
      (affRuin_psi_tendsto hb (mem_of_superset self_mem_nhdsWithin
        fun x (hx : μ < x) => lt_trans hμ hx) hF4).neg
    have hev : (fun a => -ψ a) =ᶠ[𝓝[>] μ] J := by
      filter_upwards [self_mem_nhdsWithin] with a (ha : μ < a)
      rw [hup a ha]; ring
    rw [neg_zero] at h2
    exact tendsto_nhds_unique h1 (h2.congr' hev)
  have hlow : ∀ a, 0 < a → a < μ → ψ a = -J a := by
    intro a ha haμ
    have hlim1 : Tendsto (fun b => ψ b - ψ a) (𝓝[<] μ) (𝓝 (0 - ψ a)) :=
      (affRuin_psi_tendsto hb (mem_of_superset (Ioo_mem_nhdsLT haμ)
        fun x hx => lt_trans ha hx.1) hF3).sub tendsto_const_nhds
    have hlim2 : Tendsto (fun b => J a - J b) (𝓝[<] μ) (𝓝 (J a - J μ)) :=
      tendsto_const_nhds.sub (affRuin_J_tendsto_left hg hμ)
    have hev : (fun b => ψ b - ψ a) =ᶠ[𝓝[<] μ] (fun b => J a - J b) := by
      filter_upwards [Ioo_mem_nhdsLT haμ] with b hb'
      exact ftc a b ha hb'.1.le fun x hx => by linarith [hx.2, hb'.2]
    have := tendsto_nhds_unique (hlim1.congr' hev) hlim2
    rw [hJμ] at this
    linarith
  have hall : ∀ ϑ, 0 < ϑ → ϑ ≠ μ → ψ ϑ = -J ϑ := by
    intro ϑ h0 hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hlow ϑ h0 h
    · exact hup ϑ h
  refine ⟨hall, hJμ, ?_⟩
  have h1 : Tendsto J (𝓝[>] 0) (𝓝 (J 0)) := affRuin_J_tendsto_right hg le_rfl
  have h2 : Tendsto (fun a => -ψ a) (𝓝[>] 0) (𝓝 (-0)) :=
    (affRuin_psi_tendsto hb self_mem_nhdsWithin hF2).neg
  have hev : (fun a => -ψ a) =ᶠ[𝓝[>] 0] J := by
    filter_upwards [Ioo_mem_nhdsGT hμ] with a ha
    rw [hlow a ha.1 ha.2]; ring
  rw [neg_zero] at h2
  exact tendsto_nhds_unique h1 (h2.congr' hev)

lemma affRuinP_d_integrable (P : Params) (hS : P.Standing) :
    IntegrableOn P.d (Set.Ioi 0) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h1⟩ := hS
  by_contra h
  rw [integral_undef h] at h1
  norm_num at h1

lemma affRuinP_expw (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x => a * Real.exp (-(a * x))) (Set.Ioi 0) ∧
    ∫ x in Set.Ioi (0 : ℝ), a * Real.exp (-(a * x)) = 1 := by
  have hint : IntegrableOn (fun x => a * Real.exp (-(a * x))) (Set.Ioi 0) := by
    have := (exp_neg_integrableOn_Ioi 0 ha).const_mul a
    simp only [neg_mul] at this; exact this
  refine ⟨hint, ?_⟩
  rw [integral_const_mul]
  have := integral_exp_mul_Ioi (a := -a) (by linarith) 0
  simp only [mul_zero, Real.exp_zero, neg_mul] at this
  rw [this]; field_simp

lemma affRuinP_translate (f : ℝ → ℝ) (a : ℝ) :
    ∫ y in Set.Ioi (0 : ℝ), f (a + y) = ∫ z in Set.Ioi a, f z := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_left_eq_self a (f := (Set.Ioi a).indicator f)]
  congr 1
  funext y
  by_cases hy : 0 < y
  · rw [Set.indicator_of_mem (show y ∈ Set.Ioi (0:ℝ) from hy),
      Set.indicator_of_mem (show a + y ∈ Set.Ioi a by simp [hy])]
  · rw [Set.indicator_of_notMem (show y ∉ Set.Ioi (0:ℝ) from hy),
      Set.indicator_of_notMem (show a + y ∉ Set.Ioi a by simpa using hy)]

lemma affRuinP_dle (P : Params) (hS : P.Standing) (s : Set ℝ) (hs : MeasurableSet s)
    (hsub : s ⊆ Set.Ioi 0) : ∫ y in s, P.d y ≤ 1 := by
  have hdi := affRuinP_d_integrable P hS
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hd0, -, h1⟩ := hS
  have : ∫ y in s, P.d y ≤ ∫ y in Set.Ioi 0, P.d y :=
    setIntegral_mono_set hdi ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun y _ => hd0 y)) (Filter.Eventually.of_forall hsub)
  linarith

lemma affRuinP_T1b (P : Params) (hS : P.Standing) (ρ : ℝ → ℝ)
    (hρb : ∀ x, 0 < x → |ρ x| ≤ 1) (x : ℝ) (hx : 0 < x) :
    |∫ y in Set.Ioc 0 x, P.d y * ρ (x - y)| ≤ 1 := by
  have hdi := affRuinP_d_integrable P hS
  have hd0 := hS.2.2.2.2.2.2.2.2.2.2.1
  rw [integral_Ioc_eq_integral_Ioo, ← Real.norm_eq_abs]
  refine le_trans (norm_integral_le_of_norm_le (hdi.mono_set fun y hy => hy.1)
    ((ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun y hy => ?_)))
    (affRuinP_dle P hS _ measurableSet_Ioo fun y hy => hy.1)
  have := hρb (x - y) (by linarith [hy.2])
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hd0 y)]
  exact mul_le_of_le_one_right (hd0 y) this

lemma affRuinP_T2b (P : Params) (hS : P.Standing) (x : ℝ) (hx : 0 < x) :
    |∫ y in Set.Ioi x, P.d y * Real.exp (-(P.β * (y - x))) * Real.exp (-(P.γ * x))| ≤ 1 := by
  have hdi := affRuinP_d_integrable P hS
  obtain ⟨-, -, -, -, -, -, -, hβ, hγ, -, hd0, -, -⟩ := id hS
  rw [← Real.norm_eq_abs]
  refine le_trans (norm_integral_le_of_norm_le (hdi.mono_set fun y hy => lt_trans hx hy)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)))
    (affRuinP_dle P hS _ measurableSet_Ioi fun y hy => lt_trans hx hy)
  have hy' : x < y := hy
  have e1 : Real.exp (-(P.β * (y - x))) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have e2 : Real.exp (-(P.γ * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h12 : Real.exp (-(P.β * (y - x))) * Real.exp (-(P.γ * x)) ≤ 1 := by
    nlinarith [Real.exp_pos (-(P.β * (y - x))), Real.exp_pos (-(P.γ * x))]
  have hnn : 0 ≤ P.d y * Real.exp (-(P.β * (y - x))) * Real.exp (-(P.γ * x)) :=
    mul_nonneg (mul_nonneg (hd0 y) (Real.exp_pos _).le) (Real.exp_pos _).le
  rw [Real.norm_eq_abs, abs_of_nonneg hnn, mul_assoc]
  exact mul_le_of_le_one_right (hd0 y) h12

lemma affRuinP_T3b (P : Params) (hS : P.Standing) (ρ : ℝ → ℝ)
    (hρb : ∀ x, 0 < x → |ρ x| ≤ 1) (x : ℝ) (hx : 0 < x) :
    |∫ y in Set.Ioi 0, P.μ * Real.exp (-(P.μ * y)) * ρ (x + y)| ≤ 1 := by
  have hμ : 0 < P.μ := hS.2.2.2.2.1
  obtain ⟨hμi, hμ1⟩ := affRuinP_expw P.μ hμ
  rw [← Real.norm_eq_abs, ← hμ1]
  refine norm_integral_le_of_norm_le hμi
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_))
  have hy' : (0:ℝ) < y := hy
  have := hρb (x + y) (by linarith)
  have hpos : 0 < P.μ * Real.exp (-(P.μ * y)) := mul_pos hμ (Real.exp_pos _)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
  exact mul_le_of_le_one_right hpos.le this

lemma affRuinP_T2eq (P : Params) (x : ℝ) :
    (∫ y in Set.Ioi x, P.d y * Real.exp (-(P.β * (y - x))) * Real.exp (-(P.γ * x)))
      = Real.exp (P.β * x) * Real.exp (-(P.γ * x)) *
        ∫ y in Set.Ioi x, P.d y * Real.exp (-(P.β * y)) := by
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  rw [show -(P.β * (y - x)) = P.β * x + -(P.β * y) by ring, Real.exp_add]; ring

lemma affRuinP_T2c (P : Params) (hS : P.Standing) :
    ContinuousOn (fun x => ∫ y in Set.Ioi x,
      P.d y * Real.exp (-(P.β * (y - x))) * Real.exp (-(P.γ * x))) (Set.Ioi 0) := by
  have hdi := affRuinP_d_integrable P hS
  obtain ⟨-, -, -, -, -, -, -, hβ, -, hdm, hd0, -, -⟩ := hS
  have hK2i : IntegrableOn (fun y => P.d y * Real.exp (-(P.β * y))) (Set.Ioi 0) := by
    refine Integrable.mono' hdi ((hdm.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id).neg).measurable).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
    have hy' : (0:ℝ) < y := hy
    have e1 : Real.exp (-(P.β * y)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hd0 y) (Real.exp_pos _).le)]
    exact mul_le_of_le_one_right (hd0 y) e1
  have hJ := (affRuin_J_continuousOn hK2i).mono (Set.Ioi_subset_Ici_self)
  have : ContinuousOn (fun x => Real.exp (P.β * x) * Real.exp (-(P.γ * x)) *
      ∫ y in Set.Ioi x, P.d y * Real.exp (-(P.β * y))) (Set.Ioi 0) :=
    ((by fun_prop : Continuous fun x : ℝ => Real.exp (P.β * x) *
      Real.exp (-(P.γ * x))).continuousOn).mul hJ
  exact this.congr fun x _ => affRuinP_T2eq P x

lemma affRuinP_T3eq (P : Params) (ρ : ℝ → ℝ) (x : ℝ) :
    (∫ y in Set.Ioi 0, P.μ * Real.exp (-(P.μ * y)) * ρ (x + y)) = Real.exp (P.μ * x) *
      ∫ z in Set.Ioi x, P.μ * Real.exp (-(P.μ * z)) * ρ z := by
  have := affRuinP_translate (fun z => P.μ * Real.exp (-(P.μ * (z - x))) * ρ z) x
  simp only [add_sub_cancel_left] at this
  rw [this, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun z _ => ?_
  rw [show -(P.μ * (z - x)) = P.μ * x + -(P.μ * z) by ring, Real.exp_add]; ring

lemma affRuinP_T3c (P : Params) (hS : P.Standing) (ρ : ℝ → ℝ)
    (hρb : ∀ x, 0 < x → |ρ x| ≤ 1) (hρm : AEStronglyMeasurable ρ (volume.restrict (Set.Ioi 0))) :
    ContinuousOn (fun x => ∫ y in Set.Ioi 0, P.μ * Real.exp (-(P.μ * y)) * ρ (x + y))
      (Set.Ioi 0) := by
  have hμ : 0 < P.μ := hS.2.2.2.2.1
  obtain ⟨hμi, -⟩ := affRuinP_expw P.μ hμ
  have hK3i : IntegrableOn (fun z => P.μ * Real.exp (-(P.μ * z)) * ρ z) (Set.Ioi 0) := by
    refine Integrable.mono' hμi (hμi.aestronglyMeasurable.mul hρm) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
    have := hρb y hy
    have hpos : 0 < P.μ * Real.exp (-(P.μ * y)) := mul_pos hμ (Real.exp_pos _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
    exact mul_le_of_le_one_right hpos.le this
  have hJ := (affRuin_J_continuousOn hK3i).mono (Set.Ioi_subset_Ici_self)
  have : ContinuousOn (fun x => Real.exp (P.μ * x) *
      ∫ z in Set.Ioi x, P.μ * Real.exp (-(P.μ * z)) * ρ z) (Set.Ioi 0) :=
    ((by fun_prop : Continuous fun x : ℝ => Real.exp (P.μ * x)).continuousOn).mul hJ
  exact this.congr fun x _ => affRuinP_T3eq P ρ x

lemma affRuinP_bnd {w f : ℝ → ℝ} (K : ℝ) (hwi : IntegrableOn w (Set.Ioi 0))
    (hwpos : ∀ x, 0 < w x) (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioi 0)))
    (hb : ∀ x, 0 < x → |f x| ≤ K) : IntegrableOn (fun x => f x * w x) (Set.Ioi 0) := by
  refine Integrable.mono' (hwi.const_mul K) (hf.mul hwi.aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hwpos x)]
  exact mul_le_mul_of_nonneg_right (hb x hx) (hwpos x).le

lemma affRuinP_algebra (P : Params) (hS : P.Standing) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑμ : ϑ ≠ P.μ)
    (φ φμ ρ0 dφ : ℝ)
    (key : P.r * ϑ * dφ = P.lamMinus * P.lst ϑ * φ
        + P.r * ϑ * G3 P ϑ + (P.lamPlus * (P.μ / (P.μ - ϑ)) * φ
        - P.lamPlus * (ϑ / (P.μ - ϑ)) * φμ) - (P.α + P.lam + P.ν) * φ
        - P.p * ϑ * (ρ0 - φ)) :
    dφ = F P ϑ * φ + G P ρ0 φμ ϑ := by
  have hr' : P.r ≠ 0 := hS.2.1.ne'
  have hϑ' : ϑ ≠ 0 := hϑ.ne'
  have hμϑ : P.μ - ϑ ≠ 0 := sub_ne_zero.mpr (Ne.symm hϑμ)
  simp only [F, Fbar, G, G1, G2, Params.lam] at key ⊢
  field_simp at key ⊢
  linear_combination key

theorem solution (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (hB : B.IsValid P) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑμ : ϑ ≠ P.μ) :
    HasDerivAt (phi B P)
      (F P ϑ * phi B P ϑ + G P (rho B P 0) (phi B P P.μ) ϑ) ϑ := by
  obtain ⟨hp, hr, hlp, hlm, hμ, hν, hα, -⟩ := id hS
  obtain ⟨D1, D2, D3, D4⟩ := drift_transforms P hS B hB ϑ hϑ
  obtain ⟨C1, C2⟩ := convolution_transform P hS B hB ϑ hϑ
  obtain ⟨-, R2⟩ := ruin_term_transform P hS ϑ hϑ
  have E5 := eq_5 P hS B hB ϑ hϑ hϑμ
  have L1 := fun (x : ℝ) (hx : 0 < x) => lemma_1 P hS B hB x hx
  have hρb : ∀ x, 0 < x → |rho B P x| ≤ 1 := fun x hx => affRuin_rho_abs_le_one P hS B hB x hx
  obtain ⟨w, hw⟩ : ∃ w : ℝ → ℝ, w = fun x => ϑ * Real.exp (-(ϑ * x)) := ⟨_, rfl⟩
  obtain ⟨T1, hT1⟩ : ∃ T1 : ℝ → ℝ,
      T1 = fun x => ∫ y in Set.Ioc 0 x, P.d y * rho B P (x - y) := ⟨_, rfl⟩
  obtain ⟨T2, hT2⟩ : ∃ T2 : ℝ → ℝ, T2 = fun x => ∫ y in Set.Ioi x,
      P.d y * Real.exp (-(P.β * (y - x))) * Real.exp (-(P.γ * x)) := ⟨_, rfl⟩
  obtain ⟨T3, hT3⟩ : ∃ T3 : ℝ → ℝ, T3 = fun x => ∫ y in Set.Ioi 0,
      P.μ * Real.exp (-(P.μ * y)) * rho B P (x + y) := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ → ℝ, ρ = rho B P := ⟨_, rfl⟩
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = P.α + P.lam + P.ν := ⟨_, rfl⟩
  have hc : 0 ≤ c := by rw [hc_def, Params.lam]; linarith
  -- milestone facts restated with the abbreviations
  have D1' : -(∫ x in Set.Ioi 0, deriv ρ x * P.p * w x) = P.p * ϑ * (ρ 0 - phi B P ϑ) := by
    subst hw hρ; exact D1
  have D23 : -(∫ x in Set.Ioi 0, deriv ρ x * (P.r * x) * w x) = P.r * ϑ * deriv (phi B P) ϑ := by
    subst hw hρ; rw [D2, D3]
  have C' : P.lamMinus * (∫ x in Set.Ioi 0, T1 x * w x) = P.lamMinus * P.lst ϑ * phi B P ϑ := by
    subst hw hρ hT1; rw [C1, C2]
  have R' : P.lamMinus * (∫ x in Set.Ioi 0, T2 x * w x) = P.r * ϑ * G3 P ϑ := by
    subst hw hT2; exact R2
  have E' : P.lamPlus * (∫ x in Set.Ioi 0, T3 x * w x) = P.lamPlus * (P.μ / (P.μ - ϑ)) * phi B P ϑ
      - P.lamPlus * (ϑ / (P.μ - ϑ)) * phi B P P.μ := by
    subst hw hT3; exact E5
  have hφ : ∫ x in Set.Ioi 0, ρ x * w x = phi B P ϑ := by
    subst hw hρ; simp only [phi]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    ring
  have L1' : ∀ x, 0 < x → DifferentiableAt ℝ ρ x ∧ -(deriv ρ x) * (P.p + P.r * x) =
      P.lamMinus * T1 x + P.lamMinus * T2 x + P.lamPlus * T3 x - c * ρ x := by
    intro x hx; subst hT1 hT2 hT3 hρ hc_def; exact L1 x hx
  have hρb' : ∀ x, 0 < x → |ρ x| ≤ 1 := by subst hρ; exact hρb
  have hρ0 : ρ 0 = rho B P 0 := by rw [hρ]
  clear D1 D2 D3 C1 C2 R2 E5 L1 hρb
  obtain ⟨hwi, -⟩ := affRuinP_expw ϑ hϑ
  rw [← hw] at hwi
  have hwpos : ∀ x, 0 < w x := fun x => by rw [hw]; exact mul_pos hϑ (Real.exp_pos _)
  have hρc : ContinuousOn ρ (Set.Ioi 0) :=
    fun x hx => (L1' x hx).1.continuousAt.continuousWithinAt
  have hρm : AEStronglyMeasurable ρ (volume.restrict (Set.Ioi 0)) :=
    hρc.aestronglyMeasurable measurableSet_Ioi
  have hT1b : ∀ x, 0 < x → |T1 x| ≤ 1 := fun x hx => by
    rw [hT1]; exact affRuinP_T1b P hS (rho B P) (hρ ▸ hρb') x hx
  have hT2b : ∀ x, 0 < x → |T2 x| ≤ 1 := fun x hx => by rw [hT2]; exact affRuinP_T2b P hS x hx
  have hT3b : ∀ x, 0 < x → |T3 x| ≤ 1 := fun x hx => by
    rw [hT3]; exact affRuinP_T3b P hS (rho B P) (hρ ▸ hρb') x hx
  obtain ⟨M, hM_def⟩ : ∃ M : ℝ, M = 2 * P.lamMinus + P.lamPlus + c := ⟨_, rfl⟩
  have hDb : ∀ x, 0 < x → |deriv ρ x| * (P.p + P.r * x) ≤ M := by
    intro x hx
    have heq := (L1' x hx).2
    have hpx : 0 < P.p + P.r * x := by positivity
    have b1 := abs_le.mp (show |P.lamMinus * T1 x| ≤ P.lamMinus by
      rw [abs_mul, abs_of_pos hlm]; exact mul_le_of_le_one_right hlm.le (hT1b x hx))
    have b2 := abs_le.mp (show |P.lamMinus * T2 x| ≤ P.lamMinus by
      rw [abs_mul, abs_of_pos hlm]; exact mul_le_of_le_one_right hlm.le (hT2b x hx))
    have b3 := abs_le.mp (show |P.lamPlus * T3 x| ≤ P.lamPlus by
      rw [abs_mul, abs_of_pos hlp]; exact mul_le_of_le_one_right hlp.le (hT3b x hx))
    have b4 := abs_le.mp (show |c * ρ x| ≤ c by
      rw [abs_mul, abs_of_nonneg hc]; exact mul_le_of_le_one_right hc (hρb' x hx))
    have : |deriv ρ x| * (P.p + P.r * x) = |-(deriv ρ x) * (P.p + P.r * x)| := by
      rw [abs_mul, abs_neg, abs_of_pos hpx]
    rw [this, heq, abs_le, hM_def]
    constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2]
  have hT2m : AEStronglyMeasurable T2 (volume.restrict (Set.Ioi 0)) := by
    rw [hT2]; exact (affRuinP_T2c P hS).aestronglyMeasurable measurableSet_Ioi
  have hT3m : AEStronglyMeasurable T3 (volume.restrict (Set.Ioi 0)) := by
    rw [hT3]
    exact (affRuinP_T3c P hS (rho B P) (hρ ▸ hρb') (hρ ▸ hρm)).aestronglyMeasurable
      measurableSet_Ioi
  have hDm : AEStronglyMeasurable (deriv ρ) (volume.restrict (Set.Ioi 0)) :=
    (measurable_deriv ρ).aestronglyMeasurable
  have hT1m : AEStronglyMeasurable T1 (volume.restrict (Set.Ioi 0)) := by
    have hm : AEStronglyMeasurable (fun x => (-(deriv ρ x) * (P.p + P.r * x) + c * ρ x
        - P.lamMinus * T2 x - P.lamPlus * T3 x) * P.lamMinus⁻¹) (volume.restrict (Set.Ioi 0)) :=
      ((((hDm.neg.mul (by fun_prop : Continuous fun x : ℝ => P.p + P.r * x).aestronglyMeasurable).add
        (hρm.const_mul c)).sub (hT2m.const_mul _)).sub (hT3m.const_mul _)).mul_const _
    refine hm.congr ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun x hx => ?_))
    have := (L1' x hx).2
    show (-(deriv ρ x) * (P.p + P.r * x) + c * ρ x
        - P.lamMinus * T2 x - P.lamPlus * T3 x) * P.lamMinus⁻¹ = T1 x
    rw [← div_eq_mul_inv, div_eq_iff hlm.ne']
    linear_combination this
  have iA : IntegrableOn (fun x => deriv ρ x * P.p * w x) (Set.Ioi 0) := by
    refine affRuinP_bnd M hwi hwpos (hDm.mul_const _) fun x hx => ?_
    have := hDb x hx
    rw [abs_mul, abs_of_pos hp]
    nlinarith [abs_nonneg (deriv ρ x), mul_pos hr hx]
  have iB : IntegrableOn (fun x => deriv ρ x * (P.r * x) * w x) (Set.Ioi 0) := by
    refine affRuinP_bnd M hwi hwpos
      (hDm.mul (by fun_prop : Continuous fun x : ℝ => P.r * x).aestronglyMeasurable)
      fun x hx => ?_
    have := hDb x hx
    rw [abs_mul, abs_of_pos (mul_pos hr hx)]
    nlinarith [abs_nonneg (deriv ρ x)]
  have i1 := affRuinP_bnd 1 hwi hwpos hT1m hT1b
  have i2 := affRuinP_bnd 1 hwi hwpos hT2m hT2b
  have i3 := affRuinP_bnd 1 hwi hwpos hT3m hT3b
  have i4 := affRuinP_bnd 1 hwi hwpos hρm hρb'
  have hcongr : ∫ x in Set.Ioi 0, (-(deriv ρ x * P.p * w x) - deriv ρ x * (P.r * x) * w x)
      = ∫ x in Set.Ioi 0, (P.lamMinus * (T1 x * w x) + P.lamMinus * (T2 x * w x)
          + P.lamPlus * (T3 x * w x) - c * (ρ x * w x)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have := (L1' x hx).2
    linear_combination (w x) * this
  rw [integral_sub (f := fun x => -(deriv ρ x * P.p * w x)) iA.neg iB, integral_neg,
    integral_sub (f := fun x => P.lamMinus * (T1 x * w x) + P.lamMinus * (T2 x * w x)
          + P.lamPlus * (T3 x * w x)) (g := fun x => c * (ρ x * w x))
      (((i1.const_mul _).add (i2.const_mul _)).add (i3.const_mul _)) (i4.const_mul _),
    integral_add (f := fun x => P.lamMinus * (T1 x * w x) + P.lamMinus * (T2 x * w x))
      (g := fun x => P.lamPlus * (T3 x * w x))
      ((i1.const_mul _).add (i2.const_mul _)) (i3.const_mul _),
    integral_add (f := fun x => P.lamMinus * (T1 x * w x))
      (g := fun x => P.lamMinus * (T2 x * w x)) (i1.const_mul _) (i2.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    hφ] at hcongr
  rw [← hρ0]
  have hderiv := affRuinP_algebra P hS ϑ hϑ hϑμ (phi B P ϑ) (phi B P P.μ) (ρ 0)
    (deriv (phi B P) ϑ) (by rw [← hc_def]; linarith)
  exact hderiv ▸ D4.differentiableAt.hasDerivAt
