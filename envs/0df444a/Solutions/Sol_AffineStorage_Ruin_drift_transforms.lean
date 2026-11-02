-- Prove2me | solution 1 for AffineStorage.Ruin.drift_transforms
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T00:35:51.022736+00:00
-- url     : https://prove2.me/submissions/655116c2-4c84-46c5-9396-480732454a0a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AffineStorage_Ruin_Model
import Theorems.Thm_AffineStorage_Ruin_eq_2
import Theorems.Thm_AffineStorage_Ruin_lemma_1
import Theorems.Thm_AffineStorage_Ruin_phi_infty_eq_rho_zero
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

lemma affRuinD_xexp (s x : ℝ) (hs : 0 < s) (hx : 0 ≤ x) :
    x * Real.exp (-(s * x)) ≤ 2 / s * Real.exp (-(s / 2 * x)) := by
  have h1 := Real.add_one_le_exp (s / 2 * x)
  have he : Real.exp (-(s * x)) = (Real.exp (s / 2 * x))⁻¹ * Real.exp (-(s / 2 * x)) := by
    rw [← Real.exp_neg, ← Real.exp_add]; ring_nf
  rw [he, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  have hp := Real.exp_pos (s / 2 * x)
  rw [← div_eq_mul_inv, div_le_div_iff₀ hp hs]
  nlinarith

lemma affRuinD_expint (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x => Real.exp (-(a * x))) (Set.Ioi 0) ∧
    ∫ x in Set.Ioi (0:ℝ), Real.exp (-(a * x)) = 1 / a := by
  constructor
  · have := exp_neg_integrableOn_Ioi 0 ha
    simp only [neg_mul] at this; exact this
  · have := integral_exp_mul_Ioi (a := -a) (by linarith) 0
    simp only [mul_zero, Real.exp_zero, neg_mul] at this
    rw [this]; field_simp

/-- integrability of `x e^{-sx}` on `(0,∞)`, with a bound -/
lemma affRuinD_xexp_int (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun x => x * Real.exp (-(s * x))) (Set.Ioi 0) := by
  obtain ⟨hi, -⟩ := affRuinD_expint (s / 2) (by positivity)
  refine Integrable.mono' (hi.const_mul (2 / s)) (by fun_prop : Continuous fun x : ℝ =>
    x * Real.exp (-(s * x))).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_)
  have hx' : (0:ℝ) < x := hx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx'.le (Real.exp_pos _).le)]
  exact affRuinD_xexp s x hs hx'.le

lemma affRuinD_deriv_bound (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (hB : B.IsValid P) :
    ∃ K, 0 ≤ K ∧ ∀ x, 0 < x → |deriv (rho B P) x| ≤ K := by
  obtain ⟨hp, hr, hlp, hlm, hμ, hν, hα, -⟩ := id hS
  have hρb : ∀ x, 0 < x → |rho B P x| ≤ 1 := fun x hx => affRuin_rho_abs_le_one P hS B hB x hx
  set c := P.α + P.lam + P.ν with hc_def
  have hc : 0 ≤ c := by simp only [hc_def, Params.lam]; linarith
  set M := 2 * P.lamMinus + P.lamPlus + c
  have hM : 0 ≤ M := by positivity
  refine ⟨M / P.p, by positivity, fun x hx => ?_⟩
  have heq := (lemma_1 P hS B hB x hx).2
  have hpx : 0 < P.p + P.r * x := by positivity
  have b1 := abs_le.mp (show |P.lamMinus * ∫ y in Set.Ioc 0 x, P.d y * rho B P (x - y)|
      ≤ P.lamMinus by
    rw [abs_mul, abs_of_pos hlm]
    exact mul_le_of_le_one_right hlm.le (affRuinP_T1b P hS (rho B P) hρb x hx))
  have b2 := abs_le.mp (show |P.lamMinus * ∫ y in Set.Ioi x,
      P.d y * Real.exp (-(P.β * (y - x))) * Real.exp (-(P.γ * x))| ≤ P.lamMinus by
    rw [abs_mul, abs_of_pos hlm]
    exact mul_le_of_le_one_right hlm.le (affRuinP_T2b P hS x hx))
  have b3 := abs_le.mp (show |P.lamPlus * ∫ y in Set.Ioi 0,
      P.μ * Real.exp (-(P.μ * y)) * rho B P (x + y)| ≤ P.lamPlus by
    rw [abs_mul, abs_of_pos hlp]
    exact mul_le_of_le_one_right hlp.le (affRuinP_T3b P hS (rho B P) hρb x hx))
  have b4 := abs_le.mp (show |c * rho B P x| ≤ c by
    rw [abs_mul, abs_of_nonneg hc]; exact mul_le_of_le_one_right hc (hρb x hx))
  have hDb : |deriv (rho B P) x| * (P.p + P.r * x) ≤ M := by
    have : |deriv (rho B P) x| * (P.p + P.r * x) =
        |-(deriv (rho B P) x) * (P.p + P.r * x)| := by
      rw [abs_mul, abs_neg, abs_of_pos hpx]
    rw [this, heq, abs_le]
    constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2]
  rw [le_div_iff₀ hp]
  have := abs_nonneg (deriv (rho B P) x)
  nlinarith [mul_pos hr hx]

/-- The limit `ϱ(0+)` exists and equals `ϱ(0)`, with a linear rate. -/
lemma affRuinD_rho_zero (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (hB : B.IsValid P) :
    ∃ K', 0 ≤ K' ∧ ∀ x, 0 < x → |rho B P x - rho B P 0| ≤ K' * x := by
  obtain ⟨K, hK0, hK⟩ := affRuinD_deriv_bound P hS B hB
  have hρb : ∀ x, 0 < x → |rho B P x| ≤ 1 := fun x hx => affRuin_rho_abs_le_one P hS B hB x hx
  have hdiff : ∀ x, 0 < x → HasDerivAt (rho B P) (deriv (rho B P) x) x :=
    fun x hx => (lemma_1 P hS B hB x hx).1.hasDerivAt
  have hρc : ContinuousOn (rho B P) (Set.Ioi 0) :=
    fun x hx => (hdiff x hx).continuousAt.continuousWithinAt
  have hρm : AEStronglyMeasurable (rho B P) (volume.restrict (Set.Ioi 0)) :=
    hρc.aestronglyMeasurable measurableSet_Ioi
  have hDm : Measurable (deriv (rho B P)) := measurable_deriv _
  have hDint : IntegrableOn (deriv (rho B P)) (Set.Ioc 0 1) :=
    Measure.integrableOn_of_bounded (by simp) hDm.aestronglyMeasurable (M := K)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun x hx => by
        rw [Real.norm_eq_abs]; exact hK x hx.1))
  have hDii : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      IntervalIntegrable (deriv (rho B P)) volume a b := by
    intro a b ha hab hb1
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      (hDint.mono_set (Set.Ioc_subset_Ioc ha hb1))
  set L := rho B P 1 - ∫ t in (0:ℝ)..1, deriv (rho B P) t with hL_def
  have hLx : ∀ x, 0 < x → x ≤ 1 → rho B P x - L = ∫ t in (0:ℝ)..x, deriv (rho B P) t := by
    intro x hx hx1
    have hftc : ∫ t in x..1, deriv (rho B P) t = rho B P 1 - rho B P x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hdiff t (by
        rw [Set.uIcc_of_le hx1] at ht; linarith [ht.1])) (hDii x 1 hx.le hx1 le_rfl)
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hDii 0 x le_rfl hx.le hx1) (hDii x 1 hx.le hx1 le_rfl)
    simp only [hL_def]; linarith
  have hLb : ∀ x, 0 < x → x ≤ 1 → |rho B P x - L| ≤ K * x := by
    intro x hx hx1
    rw [hLx x hx hx1, ← Real.norm_eq_abs]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x) (C := K)
      (f := deriv (rho B P)) (fun t ht => by
        rw [Set.uIoc_of_le hx.le] at ht; rw [Real.norm_eq_abs]; exact hK t ht.1)
    rwa [sub_zero, abs_of_pos hx] at this
  set K' := K + 1 + |L| with hK'
  have hK'0 : 0 ≤ K' := by positivity
  have hLb' : ∀ x, 0 < x → |rho B P x - L| ≤ K' * x := by
    intro x hx
    by_cases hx1 : x ≤ 1
    · have := hLb x hx hx1
      nlinarith [abs_nonneg L]
    · push Not at hx1
      have hb := abs_le.mp (hρb x hx)
      have h1 : |rho B P x - L| ≤ 1 + |L| :=
        abs_le.mpr ⟨by linarith [neg_abs_le L, le_abs_self L],
          by linarith [neg_abs_le L, le_abs_self L]⟩
      nlinarith [abs_nonneg L]
  -- `φ(t) → L` as `t → ∞`
  have hφL : Tendsto (phi B P) atTop (𝓝 L) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _) ?_
      (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun t : ℝ => 4 * K' / t) atTop (𝓝 0))
    filter_upwards [eventually_gt_atTop 0] with t ht
    obtain ⟨hwi, hw1⟩ := affRuinP_expw t ht
    have hρi : IntegrableOn (fun x => t * Real.exp (-(t * x)) * rho B P x) (Set.Ioi 0) := by
      refine Integrable.mono' hwi (hwi.aestronglyMeasurable.mul hρm) ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun x hx => ?_)
      have hp : 0 < t * Real.exp (-(t * x)) := mul_pos ht (Real.exp_pos _)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp]
      exact mul_le_of_le_one_right hp.le (hρb x hx)
    have heq : phi B P t - L = ∫ x in Set.Ioi 0, t * Real.exp (-(t * x)) * (rho B P x - L) := by
      have : (fun x => t * Real.exp (-(t * x)) * (rho B P x - L))
          = fun x => t * Real.exp (-(t * x)) * rho B P x - L * (t * Real.exp (-(t * x))) := by
        funext x; ring
      rw [this, integral_sub hρi (hwi.const_mul L), integral_const_mul, hw1, phi]
      ring
    obtain ⟨hei, he1⟩ := affRuinD_expint (t / 2) (by positivity)
    have hbound : ∫ x in Set.Ioi 0, 2 * K' * Real.exp (-(t / 2 * x)) = 4 * K' / t := by
      rw [integral_const_mul, he1]; field_simp; ring
    rw [heq, ← hbound]
    refine norm_integral_le_of_norm_le (hei.const_mul _) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    have hx' : (0:ℝ) < x := hx
    have hp : 0 < t * Real.exp (-(t * x)) := mul_pos ht (Real.exp_pos _)
    have h1 := hLb' x hx'
    have h2 := affRuinD_xexp t x ht hx'.le
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp]
    calc t * Real.exp (-(t * x)) * |rho B P x - L| ≤ t * Real.exp (-(t * x)) * (K' * x) :=
          mul_le_mul_of_nonneg_left h1 hp.le
      _ = t * K' * (x * Real.exp (-(t * x))) := by ring
      _ ≤ t * K' * (2 / t * Real.exp (-(t / 2 * x))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 * K' * Real.exp (-(t / 2 * x)) := by field_simp
  have hL0 : rho B P 0 = L := tendsto_nhds_unique (phi_infty_eq_rho_zero P hS B hB).1 hφL
  exact ⟨K', hK'0, fun x hx => hL0 ▸ hLb' x hx⟩

theorem solution (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (hB : B.IsValid P) (ϑ : ℝ) (hϑ : 0 < ϑ) :
    -(∫ x in Set.Ioi 0, deriv (rho B P) x * P.p * (ϑ * Real.exp (-(ϑ * x))))
        = P.p * ϑ * (rho B P 0 - phi B P ϑ) ∧
    -(∫ x in Set.Ioi 0, deriv (rho B P) x * (P.r * x) * (ϑ * Real.exp (-(ϑ * x))))
        = P.r * ϑ * ∫ x in Set.Ioi 0,
            rho B P x * (Real.exp (-(ϑ * x)) - x * (ϑ * Real.exp (-(ϑ * x)))) ∧
    P.r * ϑ * (∫ x in Set.Ioi 0,
            rho B P x * (Real.exp (-(ϑ * x)) - x * (ϑ * Real.exp (-(ϑ * x)))))
        = P.r * ϑ * deriv (phi B P) ϑ ∧
    HasDerivAt (phi B P)
      (phi B P ϑ / ϑ - ∫ x in Set.Ioi 0, x * (ϑ * Real.exp (-(ϑ * x))) * rho B P x) ϑ := by
  have hr : 0 < P.r := hS.2.1
  obtain ⟨K, hK0, hK⟩ := affRuinD_deriv_bound P hS B hB
  obtain ⟨K', hK'0, hK'⟩ := affRuinD_rho_zero P hS B hB
  have hρb : ∀ x, 0 < x → |rho B P x| ≤ 1 := fun x hx => affRuin_rho_abs_le_one P hS B hB x hx
  have hdiff : ∀ x ∈ Set.Ioi (0:ℝ), HasDerivAt (rho B P) (deriv (rho B P) x) x :=
    fun x hx => (lemma_1 P hS B hB x hx).1.hasDerivAt
  have hρc : ContinuousOn (rho B P) (Set.Ioi 0) :=
    fun x hx => (hdiff x hx).continuousAt.continuousWithinAt
  have hρm : AEStronglyMeasurable (rho B P) (volume.restrict (Set.Ioi 0)) :=
    hρc.aestronglyMeasurable measurableSet_Ioi
  have hDm : AEStronglyMeasurable (deriv (rho B P)) (volume.restrict (Set.Ioi 0)) :=
    (measurable_deriv _).aestronglyMeasurable
  obtain ⟨hei, he1⟩ := affRuinD_expint ϑ hϑ
  have hxei := affRuinD_xexp_int ϑ hϑ
  -- generic domination helper
  have dom : ∀ (f g : ℝ → ℝ), AEStronglyMeasurable f (volume.restrict (Set.Ioi 0)) →
      IntegrableOn g (Set.Ioi 0) → (∀ x, 0 < x → |f x| ≤ g x) → IntegrableOn f (Set.Ioi 0) := by
    intro f g hf hg hb
    refine Integrable.mono' hg hf ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun x hx => ?_))
    rw [Real.norm_eq_abs]; exact hb x hx
  have hρlim : Tendsto (rho B P) (𝓝[>] 0) (𝓝 (rho B P 0)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun x : ℝ => K' * x) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun x : ℝ => K' * x) (𝓝 0) (𝓝 (K' * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this; exact this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero' (Filter.Eventually.of_forall fun x => norm_nonneg _) ?_ h0
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [Real.norm_eq_abs]; exact hK' x hx
  have hexp0 : Tendsto (fun x => Real.exp (-(ϑ * x))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hϑ)
  -- conjunct 1: integration by parts with `u = ϑ e^{-ϑx}`, `v = ϱ`
  have c1 : -(∫ x in Set.Ioi 0, deriv (rho B P) x * P.p * (ϑ * Real.exp (-(ϑ * x))))
      = P.p * ϑ * (rho B P 0 - phi B P ϑ) := by
    have hu : ∀ x ∈ Set.Ioi (0:ℝ), HasDerivAt (fun x => ϑ * Real.exp (-(ϑ * x)))
        (-(ϑ * ϑ) * Real.exp (-(ϑ * x))) x := fun x _ =>
      (((hasDerivAt_id' x).const_mul ϑ).neg.exp.const_mul ϑ).congr_deriv (by simp only [Pi.neg_apply]; ring)
    have huv' : IntegrableOn (fun x => ϑ * Real.exp (-(ϑ * x)) * deriv (rho B P) x)
        (Set.Ioi 0) := by
      refine dom _ (fun x => K * (ϑ * Real.exp (-(ϑ * x))))
        ((by fun_prop : Continuous fun x : ℝ => ϑ * Real.exp (-(ϑ * x))).aestronglyMeasurable.mul
          hDm) ((hei.const_mul ϑ).const_mul K) fun x hx => ?_
      have hp : 0 < ϑ * Real.exp (-(ϑ * x)) := mul_pos hϑ (Real.exp_pos _)
      rw [abs_mul, abs_of_pos hp, mul_comm K]
      exact mul_le_mul_of_nonneg_left (hK x hx) hp.le
    have hu'v : IntegrableOn (fun x => -(ϑ * ϑ) * Real.exp (-(ϑ * x)) * rho B P x)
        (Set.Ioi 0) := by
      refine dom _ (fun x => ϑ * ϑ * Real.exp (-(ϑ * x)))
        ((by fun_prop : Continuous fun x : ℝ => -(ϑ * ϑ) * Real.exp (-(ϑ * x))).aestronglyMeasurable.mul
          hρm) (hei.const_mul _) fun x hx => ?_
      have hp : 0 < ϑ * ϑ * Real.exp (-(ϑ * x)) := by positivity
      rw [abs_mul, show -(ϑ * ϑ) * Real.exp (-(ϑ * x)) = -(ϑ * ϑ * Real.exp (-(ϑ * x))) by ring,
        abs_neg, abs_of_pos hp]
      exact mul_le_of_le_one_right hp.le (hρb x hx)
    have h_zero : Tendsto ((fun x => ϑ * Real.exp (-(ϑ * x))) * rho B P) (𝓝[>] 0)
        (𝓝 (ϑ * rho B P 0)) := by
      have hc : Tendsto (fun x => ϑ * Real.exp (-(ϑ * x))) (𝓝[>] 0) (𝓝 ϑ) := by
        have : Tendsto (fun x => ϑ * Real.exp (-(ϑ * x))) (𝓝 0) (𝓝 (ϑ * Real.exp (-(ϑ * 0)))) :=
          ((by fun_prop : Continuous fun x : ℝ => ϑ * Real.exp (-(ϑ * x)))).tendsto 0
        simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at this
        exact this.mono_left nhdsWithin_le_nhds
      exact hc.mul hρlim
    have h_infty : Tendsto ((fun x => ϑ * Real.exp (-(ϑ * x))) * rho B P) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ (by simpa using hexp0.const_mul ϑ)
      filter_upwards [eventually_gt_atTop 0] with x hx
      have hp : 0 < ϑ * Real.exp (-(ϑ * x)) := mul_pos hϑ (Real.exp_pos _)
      simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_pos hp]
      have := hρb x hx
      nlinarith [Real.exp_pos (-(ϑ * x))]
    have ibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hdiff huv' hu'v h_zero h_infty
    have hA : ∫ x in Set.Ioi 0, deriv (rho B P) x * P.p * (ϑ * Real.exp (-(ϑ * x)))
        = P.p * ∫ x in Set.Ioi 0, ϑ * Real.exp (-(ϑ * x)) * deriv (rho B P) x := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      ring
    have hB' : ∫ x in Set.Ioi 0, -(ϑ * ϑ) * Real.exp (-(ϑ * x)) * rho B P x
        = -ϑ * phi B P ϑ := by
      rw [phi, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      ring
    rw [hA, ibp, hB']
    ring
  -- conjunct 2: integration by parts with `u = r x ϑ e^{-ϑx}`
  have c2 : -(∫ x in Set.Ioi 0, deriv (rho B P) x * (P.r * x) * (ϑ * Real.exp (-(ϑ * x))))
      = P.r * ϑ * ∫ x in Set.Ioi 0,
          rho B P x * (Real.exp (-(ϑ * x)) - x * (ϑ * Real.exp (-(ϑ * x)))) := by
    set u : ℝ → ℝ := fun x => P.r * x * (ϑ * Real.exp (-(ϑ * x))) with hu_def
    set u' : ℝ → ℝ := fun x => P.r * ϑ * (Real.exp (-(ϑ * x)) - x * (ϑ * Real.exp (-(ϑ * x))))
      with hu'_def
    have hu : ∀ x ∈ Set.Ioi (0:ℝ), HasDerivAt u (u' x) x := fun x _ =>
      (((hasDerivAt_id' x).const_mul P.r).mul
        (((hasDerivAt_id' x).const_mul ϑ).neg.exp.const_mul ϑ)).congr_deriv (by simp only [hu'_def, Pi.neg_apply]; ring)
    have hxe : ∀ x, 0 < x → 0 ≤ x * Real.exp (-(ϑ * x)) :=
      fun x hx => mul_nonneg hx.le (Real.exp_pos _).le
    have huv' : IntegrableOn (fun x => u x * deriv (rho B P) x) (Set.Ioi 0) := by
      refine dom _ (fun x => K * (P.r * ϑ) * (x * Real.exp (-(ϑ * x))))
        ((by simp only [hu_def]; fun_prop : Continuous u).aestronglyMeasurable.mul hDm)
        (hxei.const_mul _) fun x hx => ?_
      have hp : 0 ≤ u x := by simp only [hu_def]; have := hxe x hx; positivity
      rw [abs_mul, abs_of_nonneg hp]
      calc u x * |deriv (rho B P) x| ≤ u x * K := mul_le_mul_of_nonneg_left (hK x hx) hp
        _ = _ := by simp only [hu_def]; ring
    have hu'v : IntegrableOn (fun x => u' x * rho B P x) (Set.Ioi 0) := by
      refine dom _ (fun x => P.r * ϑ * (Real.exp (-(ϑ * x)) + ϑ * (x * Real.exp (-(ϑ * x)))))
        ((by simp only [hu'_def]; fun_prop : Continuous u').aestronglyMeasurable.mul hρm)
        ((hei.add (hxei.const_mul ϑ)).const_mul _) fun x hx => ?_
      have hb := hρb x hx
      have hxe' := hxe x hx
      have hpe := Real.exp_pos (-(ϑ * x))
      have hu'b : |u' x| ≤ P.r * ϑ * (Real.exp (-(ϑ * x)) + ϑ * (x * Real.exp (-(ϑ * x)))) := by
        simp only [hu'_def]
        rw [abs_mul, abs_of_pos (mul_pos hr hϑ)]
        refine mul_le_mul_of_nonneg_left ?_ (mul_pos hr hϑ).le
        rw [abs_le]; constructor <;> nlinarith
      rw [abs_mul]
      calc |u' x| * |rho B P x| ≤ |u' x| * 1 := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ ≤ _ := by rw [mul_one]; exact hu'b
    have hub : ∀ x, 0 < x → |u x| ≤ P.r * ϑ * (2 / ϑ * Real.exp (-(ϑ / 2 * x))) := by
      intro x hx
      have hp : 0 ≤ u x := by simp only [hu_def]; have := hxe x hx; positivity
      rw [abs_of_nonneg hp]
      have := affRuinD_xexp ϑ x hϑ hx.le
      calc u x = P.r * ϑ * (x * Real.exp (-(ϑ * x))) := by simp only [hu_def]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this (mul_pos hr hϑ).le
    have h_zero : Tendsto (u * rho B P) (𝓝[>] 0) (𝓝 0) := by
      have hc : Tendsto u (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto u (𝓝 0) (𝓝 (u 0)) :=
          ((by simp only [hu_def]; fun_prop : Continuous u)).tendsto 0
        simp only [hu_def, mul_zero, zero_mul] at this
        exact this.mono_left nhdsWithin_le_nhds
      refine squeeze_zero_norm' ?_ (hc.norm.trans_eq (by simp) : Tendsto (fun x => ‖u x‖) _ (𝓝 0))
      filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
      simp only [Pi.mul_apply, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (by rw [Real.norm_eq_abs]; exact hρb x hx)
    have h_infty : Tendsto (u * rho B P) atTop (𝓝 0) := by
      have hexp2 : Tendsto (fun x => P.r * ϑ * (2 / ϑ * Real.exp (-(ϑ / 2 * x)))) atTop (𝓝 0) := by
        have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (tendsto_id.const_mul_atTop (by positivity : (0:ℝ) < ϑ / 2))).const_mul (P.r * ϑ * (2 / ϑ))
        simp only [mul_zero] at this
        refine this.congr fun x => ?_
        simp only [Function.comp, id]; ring
      refine squeeze_zero_norm' ?_ hexp2
      filter_upwards [eventually_gt_atTop 0] with x hx
      simp only [Pi.mul_apply, norm_mul, Real.norm_eq_abs]
      calc |u x| * |rho B P x| ≤ |u x| * 1 := mul_le_mul_of_nonneg_left (hρb x hx) (abs_nonneg _)
        _ ≤ _ := by rw [mul_one]; exact hub x hx
    have ibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hdiff huv' hu'v h_zero h_infty
    have hA : ∫ x in Set.Ioi 0, deriv (rho B P) x * (P.r * x) * (ϑ * Real.exp (-(ϑ * x)))
        = ∫ x in Set.Ioi 0, u x * deriv (rho B P) x := by
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      simp only [hu_def]; ring
    have hB' : ∫ x in Set.Ioi 0, u' x * rho B P x = P.r * ϑ * ∫ x in Set.Ioi 0,
          rho B P x * (Real.exp (-(ϑ * x)) - x * (ϑ * Real.exp (-(ϑ * x)))) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      simp only [hu'_def]; ring
    rw [hA, ibp, hB']
    ring
  -- conjuncts 3, 4: differentiation under the integral sign
  have hderiv : HasDerivAt (phi B P) (∫ x in Set.Ioi 0,
      rho B P x * (Real.exp (-(ϑ * x)) - x * (ϑ * Real.exp (-(ϑ * x))))) ϑ := by
    obtain ⟨he2, -⟩ := affRuinD_expint (ϑ / 2) (by positivity)
    obtain ⟨he4, -⟩ := affRuinD_expint (ϑ / 4) (by positivity)
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Set.Ioi 0))
      (F := fun t x => t * Real.exp (-(t * x)) * rho B P x)
      (F' := fun t x => rho B P x * (Real.exp (-(t * x)) - x * (t * Real.exp (-(t * x)))))
      (x₀ := ϑ) (s := Metric.ball ϑ (ϑ / 2))
      (bound := fun x => Real.exp (-(ϑ / 2 * x)) + 6 * Real.exp (-(ϑ / 4 * x)))
      (Metric.ball_mem_nhds ϑ (by positivity))
      (Filter.Eventually.of_forall fun t =>
        ((by fun_prop : Continuous fun x : ℝ => t * Real.exp (-(t * x))).aestronglyMeasurable.mul hρm))
      (dom _ (fun x => ϑ * Real.exp (-(ϑ * x)))
        ((by fun_prop : Continuous fun x : ℝ => ϑ * Real.exp (-(ϑ * x))).aestronglyMeasurable.mul hρm)
        (hei.const_mul ϑ) fun x hx => by
          have hp : 0 < ϑ * Real.exp (-(ϑ * x)) := mul_pos hϑ (Real.exp_pos _)
          rw [abs_mul, abs_of_pos hp]
          exact mul_le_of_le_one_right hp.le (hρb x hx))
      (hρm.mul (by fun_prop : Continuous fun x : ℝ =>
        Real.exp (-(ϑ * x)) - x * (ϑ * Real.exp (-(ϑ * x)))).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx t ht => by
        have hx' : (0:ℝ) < x := hx
        rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
        have ht1 : ϑ / 2 < t := by linarith [ht.1]
        have ht2 : t < 3 * ϑ / 2 := by linarith [ht.2]
        have e1 : Real.exp (-(t * x)) ≤ Real.exp (-(ϑ / 2 * x)) :=
          Real.exp_le_exp.mpr (by nlinarith)
        have e2 : x * Real.exp (-(ϑ / 2 * x)) ≤ 2 / (ϑ / 2) * Real.exp (-(ϑ / 2 / 2 * x)) :=
          affRuinD_xexp (ϑ / 2) x (by positivity) hx'.le
        have e3 : 2 / (ϑ / 2) * Real.exp (-(ϑ / 2 / 2 * x)) = 4 / ϑ * Real.exp (-(ϑ / 4 * x)) := by
          congr 1
          · field_simp; ring
          · ring_nf
        have hb := hρb x hx'
        have hpe := Real.exp_pos (-(t * x))
        have hpe2 := Real.exp_pos (-(ϑ / 2 * x))
        rw [Real.norm_eq_abs, abs_mul]
        have hin : |Real.exp (-(t * x)) - x * (t * Real.exp (-(t * x)))|
            ≤ Real.exp (-(ϑ / 2 * x)) + 6 * Real.exp (-(ϑ / 4 * x)) := by
          have h1 : x * (t * Real.exp (-(t * x))) ≤ 3 * ϑ / 2 * (x * Real.exp (-(ϑ / 2 * x))) := by
            have : x * Real.exp (-(t * x)) ≤ x * Real.exp (-(ϑ / 2 * x)) :=
              mul_le_mul_of_nonneg_left e1 hx'.le
            nlinarith [mul_nonneg hx'.le hpe.le]
          have h2 : 3 * ϑ / 2 * (x * Real.exp (-(ϑ / 2 * x))) ≤ 6 * Real.exp (-(ϑ / 4 * x)) := by
            have := mul_le_mul_of_nonneg_left (e2.trans e3.le) (by positivity : (0:ℝ) ≤ 3 * ϑ / 2)
            calc 3 * ϑ / 2 * (x * Real.exp (-(ϑ / 2 * x))) ≤ 3 * ϑ / 2 * (4 / ϑ *
                  Real.exp (-(ϑ / 4 * x))) := this
              _ = 6 * Real.exp (-(ϑ / 4 * x)) := by field_simp; ring
          have h3 : 0 ≤ x * (t * Real.exp (-(t * x))) :=
            mul_nonneg hx'.le (mul_nonneg (by linarith) hpe.le)
          rw [abs_le]; constructor <;> linarith
        calc |rho B P x| * |Real.exp (-(t * x)) - x * (t * Real.exp (-(t * x)))|
            ≤ 1 * (Real.exp (-(ϑ / 2 * x)) + 6 * Real.exp (-(ϑ / 4 * x))) :=
              mul_le_mul hb hin (abs_nonneg _) zero_le_one
          _ = _ := one_mul _))
      (he2.add (he4.const_mul 6))
      (Filter.Eventually.of_forall fun x t _ =>
        ((((hasDerivAt_id' t).mul (((hasDerivAt_id' t).mul_const x).neg.exp)).mul_const
          (rho B P x)).congr_deriv (by simp only [Pi.neg_apply]; ring)))
    have hφeq : phi B P = fun t => ∫ x in Set.Ioi 0, t * Real.exp (-(t * x)) * rho B P x := by
      funext t; rfl
    rw [hφeq]
    exact key.2
  have c3 : deriv (phi B P) ϑ = ∫ x in Set.Ioi 0,
      rho B P x * (Real.exp (-(ϑ * x)) - x * (ϑ * Real.exp (-(ϑ * x)))) := hderiv.deriv
  refine ⟨c1, c2, by rw [c3], ?_⟩
  -- conjunct 4: rewrite the derivative
  have hi1 : IntegrableOn (fun x => rho B P x * Real.exp (-(ϑ * x))) (Set.Ioi 0) :=
    dom _ (fun x => Real.exp (-(ϑ * x))) (hρm.mul (by fun_prop : Continuous fun x : ℝ =>
      Real.exp (-(ϑ * x))).aestronglyMeasurable) hei fun x hx => by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_of_le_one_left (Real.exp_pos _).le (hρb x hx)
  have hi2 : IntegrableOn (fun x => x * (ϑ * Real.exp (-(ϑ * x))) * rho B P x) (Set.Ioi 0) :=
    dom _ (fun x => ϑ * (x * Real.exp (-(ϑ * x)))) ((by fun_prop : Continuous fun x : ℝ =>
      x * (ϑ * Real.exp (-(ϑ * x)))).aestronglyMeasurable.mul hρm) (hxei.const_mul ϑ) fun x hx => by
        have hp : 0 ≤ x * (ϑ * Real.exp (-(ϑ * x))) := by
          have := Real.exp_pos (-(ϑ * x)); have : (0:ℝ) ≤ x := le_of_lt hx; positivity
        rw [abs_mul, abs_of_nonneg hp]
        calc x * (ϑ * Real.exp (-(ϑ * x))) * |rho B P x| ≤ x * (ϑ * Real.exp (-(ϑ * x))) * 1 :=
              mul_le_mul_of_nonneg_left (hρb x hx) hp
          _ = _ := by ring
  have hval : (∫ x in Set.Ioi 0,
      rho B P x * (Real.exp (-(ϑ * x)) - x * (ϑ * Real.exp (-(ϑ * x)))))
      = phi B P ϑ / ϑ - ∫ x in Set.Ioi 0, x * (ϑ * Real.exp (-(ϑ * x))) * rho B P x := by
    have hφ : phi B P ϑ / ϑ = ∫ x in Set.Ioi 0, rho B P x * Real.exp (-(ϑ * x)) := by
      rw [phi, eq_comm, eq_div_iff hϑ.ne', ← integral_mul_const]
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      ring
    rw [hφ, ← integral_sub hi1 hi2]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    ring
  rw [← hval]
  exact hderiv
