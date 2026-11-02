-- Prove2me | solution 1 for AffineStorage.Ruin.eq_9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T00:03:20.59555+00:00
-- url     : https://prove2.me/submissions/c05aaebe-e8cf-47ae-a44f-c962284bf9d3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AffineStorage_Ruin_Model
import Theorems.Thm_AffineStorage_Ruin_eq_2
import Theorems.Thm_AffineStorage_Ruin_proposition_1
import Theorems.Thm_AffineStorage_Ruin_Fstar_tendsto
import Theorems.Thm_AffineStorage_Ruin_remark_3
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

theorem solution (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (hB : B.IsValid P) (Fs : ℝ → ℝ) (hF : IsPrimitiveF P Fs) :
    ∀ ϑ, 0 < ϑ → ϑ ≠ P.μ →
      phi B P ϑ = -(∫ η in Set.Ioi ϑ,
          G P (rho B P 0) (phi B P P.μ) η * Real.exp (-(Fs η))) * Real.exp (Fs ϑ) := by
  have hμ : 0 < P.μ := hS.2.2.2.2.1
  obtain ⟨-, hF1, hF2, hF3, hF4⟩ := Fstar_tendsto P hS Fs hF
  obtain ⟨hi1, hi2, hi3⟩ := remark_3 P hS Fs hF
  set g := fun η => G P (rho B P 0) (phi B P P.μ) η * Real.exp (-(Fs η)) with hg_def
  have hg : IntegrableOn g (Set.Ioi 0) := by
    have := ((hi1.const_mul (rho B P 0)).add (hi2.const_mul (phi B P P.μ))).add hi3
    refine IntegrableOn.congr_fun this (fun η _ => ?_) measurableSet_Ioi
    simp only [hg_def, G, Pi.add_apply]; ring
  have hd : ∀ ϑ, 0 < ϑ → ϑ ≠ P.μ →
      HasDerivAt (fun t => phi B P t * Real.exp (-(Fs t))) (g ϑ) ϑ := by
    intro ϑ h0 hne
    have h1 := proposition_1 P hS B hB ϑ h0 hne
    have h2 := (hF ϑ h0 hne).neg.exp
    refine (h1.mul h2).congr_deriv ?_
    simp only [hg_def, Pi.neg_apply]; ring
  obtain ⟨hall, -, -⟩ := affRuin_core hμ hd hg (affRuin_phi_abs_le_one P hS B hB)
    hF1 hF2 hF3 hF4
  intro ϑ h0 hne
  have h := hall ϑ h0 hne
  have he : Real.exp (-(Fs ϑ)) * Real.exp (Fs ϑ) = 1 := by
    rw [← Real.exp_add]; simp
  calc phi B P ϑ = (phi B P ϑ * Real.exp (-(Fs ϑ))) * Real.exp (Fs ϑ) := by
        rw [mul_assoc, he, mul_one]
    _ = _ := by rw [h]
