-- Prove2me | solution 1 for AsyncSA.Contraction.theorem1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T11:36:05.805116+00:00
-- url     : https://prove2.me/submissions/d07d343e-165a-4648-a7c9-cfb5c00a1cab

import Mathlib
import Definitions.Def_AsyncSA_Contraction_Model
import Theorems.Thm_AsyncSA_Contraction_lemma2
import Theorems.Thm_AsyncSA_Contraction_lemma3

open MeasureTheory Filter Topology
open AsyncSA.Contraction

namespace AsyncSA.Contraction.Thm1Aux

/-- Weighted form of the conditional second-moment bound. -/
lemma wsq {Ω : Type*} (m : MeasurableSpace Ω) [m₀ : MeasurableSpace Ω] (hm : m ≤ m₀)
    (P : Measure Ω) (f h : Ω → ℝ) (hf : Measurable f) (hh : Measurable h)
    (H : ∀ S, MeasurableSet[m] S →
      ∫⁻ ω in S, ENNReal.ofReal (f ω ^ 2) ∂P ≤ ∫⁻ ω in S, ENNReal.ofReal (h ω) ∂P)
    (g : Ω → ENNReal) (hg : Measurable[m] g) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) * g ω ∂P ≤ ∫⁻ ω, ENNReal.ofReal (h ω) * g ω ∂P := by
  have m1 : Measurable fun ω => ENNReal.ofReal (f ω ^ 2) := (hf.pow_const 2).ennreal_ofReal
  have m2 : Measurable fun ω => ENNReal.ofReal (h ω) := hh.ennreal_ofReal
  have hle : (P.withDensity fun ω => ENNReal.ofReal (f ω ^ 2)).trim hm ≤
      (P.withDensity fun ω => ENNReal.ofReal (h ω)).trim hm := by
    refine Measure.le_intro fun S hS _ => ?_
    rw [trim_measurableSet_eq hm hS, trim_measurableSet_eq hm hS,
      withDensity_apply _ (hm _ hS), withDensity_apply _ (hm _ hS)]
    exact H S hS
  have := lintegral_mono' hle (le_refl g)
  rw [lintegral_trim hm hg, lintegral_trim hm hg,
    lintegral_withDensity_eq_lintegral_mul _ m1 (hg.mono hm le_rfl),
    lintegral_withDensity_eq_lintegral_mul _ m2 (hg.mono hm le_rfl)] at this
  simpa [Pi.mul_apply] using this



/-- Multiplying martingale-difference noise by a bounded `m`-measurable factor. -/
lemma cmz_mul {Ω : Type*} (m : MeasurableSpace Ω) [m₀ : MeasurableSpace Ω] (hm : m ≤ m₀)
    (P : Measure Ω) [IsProbabilityMeasure P] (w h B : Ω → ℝ) (hw : Measurable w)
    (hh : Measurable[m] h) (hB : Measurable[m] B) (H : ℝ) (hH : ∀ ω, |h ω| ≤ H)
    (hmean : CondMeanZero m₀ m P w) (hsq : CondSqLe m₀ m P w B) :
    CondMeanZero m₀ m P (fun ω => h ω * w ω) ∧
      CondSqLe m₀ m P (fun ω => h ω * w ω) (fun ω => h ω ^ 2 * B ω) := by
  classical
  obtain ⟨hBnn, hle⟩ := hsq
  have hB0 : Measurable B := hB.mono hm le_rfl
  have hh0 : Measurable h := hh.mono hm le_rfl
  refine ⟨?_, ?_, ?_⟩
  · intro S hS hfin
    let A : ℕ → Set Ω := fun N => {ω | B ω ≤ N}
    have hA : ∀ N, MeasurableSet[m] (A N) := fun N => measurableSet_le hB measurable_const
    let u : ℕ → Ω → ℝ := fun N => (A N).indicator w
    have hum : ∀ N, Measurable (u N) := fun N => hw.indicator (hm _ (hA N))
    have hu : ∀ N, Integrable (u N) P := by
      intro N
      have hL : MemLp (u N) 2 P := by
        rw [memLp_two_iff_integrable_sq (hum N).aestronglyMeasurable]
        refine ⟨((hum N).pow_const 2).aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => sq_nonneg _)]
        have hg : Measurable[m] ((A N).indicator fun _ => (1 : ENNReal)) :=
          measurable_const.indicator (hA N)
        have h1 := wsq m hm P w B hw hB0 hle _ hg
        calc ∫⁻ ω, ENNReal.ofReal (u N ω ^ 2) ∂P
            = ∫⁻ ω, ENNReal.ofReal (w ω ^ 2) * (A N).indicator (fun _ => (1 : ENNReal)) ω ∂P := by
              refine lintegral_congr fun ω => ?_
              by_cases hω : ω ∈ A N
              · simp [u, Set.indicator_of_mem hω]
              · simp [u, Set.indicator_of_notMem hω]
          _ ≤ ∫⁻ ω, ENNReal.ofReal (B ω) * (A N).indicator (fun _ => (1 : ENNReal)) ω ∂P := h1
          _ ≤ ∫⁻ ω, ENNReal.ofReal N ∂P := by
              refine lintegral_mono fun ω => ?_
              by_cases hω : ω ∈ A N
              · simp only [Set.indicator_of_mem hω, mul_one]
                exact ENNReal.ofReal_le_ofReal hω
              · simp [Set.indicator_of_notMem hω]
          _ < ⊤ := by simp
      exact hL.integrable one_le_two
    have hu_ce : ∀ N, P[u N | m] =ᵐ[P] 0 := by
      intro N
      refine (ae_eq_condExp_of_forall_setIntegral_eq hm (hu N)
        (fun S _ _ => integrableOn_zero) (fun S' hS' _ => ?_)
        stronglyMeasurable_zero.aestronglyMeasurable).symm
      rw [setIntegral_indicator (hm _ (hA N))]
      simp only [integral_zero]
      symm
      apply hmean (S' ∩ A N) (hS'.inter (hA N))
      calc ∫⁻ ω in S' ∩ A N, ‖w ω‖ₑ ∂P
          = ∫⁻ ω in S' ∩ A N, ‖u N ω‖ₑ ∂P := by
            refine setLIntegral_congr_fun (hm _ (hS'.inter (hA N))) fun ω hω => ?_
            simp only [u, Set.indicator_of_mem hω.2]
        _ ≤ ∫⁻ ω, ‖u N ω‖ₑ ∂P := setLIntegral_le_lintegral _ _
        _ < ⊤ := (hu N).2
    have hzero : ∀ N, ∫ ω in S, h ω * u N ω ∂P = 0 := by
      intro N
      have e1 : ∫ ω in S, h ω * u N ω ∂P = ∫ ω, (S.indicator h * u N) ω ∂P := by
        rw [← integral_indicator (hm _ hS)]
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        by_cases hω : ω ∈ S
        · simp [Set.indicator_of_mem hω]
        · simp [Set.indicator_of_notMem hω]
      have hSm : StronglyMeasurable[m] (S.indicator h) := (hh.indicator hS).stronglyMeasurable
      have hint : Integrable (S.indicator h * u N) P := by
        refine Integrable.bdd_mul (c := H) (hu N)
          ((hh0.indicator (hm _ hS)).aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
        by_cases hω : ω ∈ S
        · simp only [Set.indicator_of_mem hω, Real.norm_eq_abs]; exact hH ω
        · simp only [Set.indicator_of_notMem hω, norm_zero]
          exact le_trans (abs_nonneg _) (hH ω)
      rw [e1, ← integral_condExp hm]
      have h1 := condExp_mul_of_stronglyMeasurable_left (m := m) (μ := P) hSm hint (hu N)
      have h2 : (S.indicator h * P[u N | m]) =ᵐ[P] 0 := by
        filter_upwards [hu_ce N] with ω hω
        simp [hω]
      calc ∫ ω, (P[S.indicator h * u N | m]) ω ∂P = ∫ ω, (0 : Ω → ℝ) ω ∂P :=
            integral_congr_ae (h1.trans h2)
        _ = 0 := by simp
    have hint : Integrable (fun ω => h ω * w ω) (P.restrict S) :=
      ⟨(hh0.mul hw).aestronglyMeasurable, hfin⟩
    have hlim := tendsto_integral_of_dominated_convergence (μ := P.restrict S)
      (F := fun N ω => h ω * u N ω) (f := fun ω => h ω * w ω)
      (fun ω => |h ω * w ω|)
      (fun N => (hh0.mul (hum N)).aestronglyMeasurable) hint.abs
      (fun N => ae_of_all _ fun ω => by
        by_cases hω : ω ∈ A N
        · simp [u, Set.indicator_of_mem hω]
        · simp [u, Set.indicator_of_notMem hω]; positivity)
      (ae_of_all _ fun ω => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop ⌈B ω⌉₊] with N hN
        have hω : ω ∈ A N := by
          show B ω ≤ (N : ℝ)
          exact le_trans (Nat.le_ceil (B ω)) (by exact_mod_cast hN)
        simp [u, Set.indicator_of_mem hω])
    simp_rw [hzero] at hlim
    exact (tendsto_nhds_unique hlim tendsto_const_nhds)
  · filter_upwards [hBnn] with ω hω
    exact mul_nonneg (sq_nonneg _) hω
  · intro S hS
    have hg : Measurable[m] (S.indicator fun ω => ENNReal.ofReal (h ω ^ 2)) :=
      ((hh.pow_const 2).ennreal_ofReal).indicator hS
    have h1 := wsq m hm P w B hw hB0 hle _ hg
    rw [← lintegral_indicator (hm _ hS), ← lintegral_indicator (hm _ hS)]
    calc ∫⁻ ω, S.indicator (fun ω => ENNReal.ofReal ((h ω * w ω) ^ 2)) ω ∂P
        = ∫⁻ ω, ENNReal.ofReal (w ω ^ 2) *
            S.indicator (fun ω => ENNReal.ofReal (h ω ^ 2)) ω ∂P := by
          refine lintegral_congr fun ω => ?_
          by_cases hω : ω ∈ S
          · simp only [Set.indicator_of_mem hω]
            rw [← ENNReal.ofReal_mul (sq_nonneg _)]; congr 1; ring
          · simp [Set.indicator_of_notMem hω]
      _ ≤ ∫⁻ ω, ENNReal.ofReal (B ω) *
            S.indicator (fun ω => ENNReal.ofReal (h ω ^ 2)) ω ∂P := h1
      _ = ∫⁻ ω, S.indicator (fun ω => ENNReal.ofReal (h ω ^ 2 * B ω)) ω ∂P := by
          refine lintegral_congr fun ω => ?_
          by_cases hω : ω ∈ S
          · simp only [Set.indicator_of_mem hω]
            rw [ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
          · simp [Set.indicator_of_notMem hω]

lemma wNorm_eq_norm {n : ℕ} (hn : 0 < n) (v z : Fin n → ℝ) (hv : ∀ i, 0 < v i) :
    wNorm v z = ‖fun i => z i / v i‖ := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hb : BddAbove (Set.range fun i => |z i| / v i) := Finite.bddAbove_range _
  show (⨆ i, |z i| / v i) = _
  have h0 : 0 ≤ ⨆ i, |z i| / v i :=
    le_trans (div_nonneg (abs_nonneg _) (hv ⟨0, hn⟩).le) (le_ciSup hb ⟨0, hn⟩)
  apply le_antisymm
  · apply ciSup_le; intro i
    have := norm_le_pi_norm (fun i => z i / v i) i
    simpa [Real.norm_eq_abs, abs_div, abs_of_pos (hv i)] using this
  · refine (pi_norm_le_iff_of_nonneg h0).2 fun i => ?_
    simp only [Real.norm_eq_abs, abs_div, abs_of_pos (hv i)]
    exact le_ciSup hb i

lemma norm_eq_iSup {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ) : ‖y‖ = ⨆ j, |y j| := by
  have := wNorm_eq_norm hn (fun _ => (1:ℝ)) y (fun _ => one_pos)
  simpa [wNorm] using this.symm

/-- Coordinate scaling `x_i ↦ x_i / v_i`. -/
noncomputable def scale {n : ℕ} {Ω : Type*} (alg : Algorithm n Ω) (v : Fin n → ℝ)
    (hv : ∀ i, 0 < v i) : Algorithm n Ω where
  n_pos := alg.n_pos
  F := fun y i => alg.F (fun j => v j * y j) i / v i
  x := fun t ω i => alg.x t ω i / v i
  α := alg.α
  w := fun i t ω => alg.w i t ω / v i
  τ := alg.τ
  α_mem := alg.α_mem
  τ_le := alg.τ_le
  update := by
    intro i t ω
    have hfun : (fun j => v j * (alg.x (alg.τ i j t ω) ω j / v j))
        = fun j => alg.x (alg.τ i j t ω) ω j := by
      funext j; field_simp [(hv j).ne']
    dsimp only
    rw [hfun, alg.update i t ω]
    field_simp [(hv i).ne']

lemma abs_le_runMax {n : ℕ} {Ω : Type*} (alg : Algorithm n Ω) (ω : Ω) {s t : ℕ} (hst : s ≤ t)
    (j : Fin n) : |alg.x s ω j| ≤ alg.runMax t ω := by
  unfold Algorithm.runMax
  have hb1 : BddAbove (Set.range fun j => |alg.x s ω j|) := Finite.bddAbove_range _
  have hb2 : BddAbove (Set.range fun s : Fin (t + 1) => ⨆ j, |alg.x s ω j|) :=
    Finite.bddAbove_range _
  have h2 := le_ciSup hb2 ⟨s, by omega⟩
  exact le_trans (le_ciSup hb1 j) h2

lemma runMax_nonneg {n : ℕ} {Ω : Type*} (alg : Algorithm n Ω) (t : ℕ) (ω : Ω) :
    0 ≤ alg.runMax t ω := by
  unfold Algorithm.runMax
  exact Real.iSup_nonneg fun s => Real.iSup_nonneg fun j => abs_nonneg _

lemma runMax_le {n : ℕ} {Ω : Type*} (alg : Algorithm n Ω) (t : ℕ) (ω : Ω) (b : ℝ)
    (hb : 0 ≤ b) (h : ∀ s ≤ t, ∀ j, |alg.x s ω j| ≤ b) : alg.runMax t ω ≤ b := by
  unfold Algorithm.runMax
  exact Real.iSup_le (fun s => Real.iSup_le (fun j => h s (by omega) j) hb) hb

lemma runMax_mono {n : ℕ} {Ω : Type*} (alg : Algorithm n Ω) (ω : Ω) {t t' : ℕ} (h : t ≤ t') :
    alg.runMax t ω ≤ alg.runMax t' ω :=
  runMax_le alg t ω _ (runMax_nonneg alg t' ω) fun s hs j =>
    abs_le_runMax alg ω (le_trans hs h) j

lemma exists_k (G0 c r : ℝ) (hG0 : 0 < G0) (hc : 1 < c) : ∃ k : ℕ, r ≤ G0 * c ^ k := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (r / G0) hc
  refine ⟨k, ?_⟩
  rw [div_lt_iff₀ hG0] at hk
  linarith

/-- The exponent of the jump in the proof of Theorem 1. -/
noncomputable def kfun (G0 c : ℝ) (hG0 : 0 < G0) (hc : 1 < c) (r : ℝ) : ℕ :=
  Nat.find (exists_k G0 c r hG0 hc)

lemma kfun_meas (G0 c : ℝ) (hG0 : 0 < G0) (hc : 1 < c) : Measurable (kfun G0 c hG0 hc) :=
  measurable_find (p := fun r k => r ≤ G0 * c ^ k) (fun r => exists_k G0 c r hG0 hc)
    fun k => measurableSet_Iic

/-- The scale process `G(t)` of the proof of Theorem 1. -/
noncomputable def Gp {Ω : Type*} (R : ℕ → Ω → ℝ) (G0 c : ℝ) (hG0 : 0 < G0) (hc : 1 < c) :
    ℕ → Ω → ℝ
  | 0 => fun ω => max (R 0 ω) G0
  | t + 1 => fun ω => if R (t + 1) ω ≤ c * Gp R G0 c hG0 hc t ω then Gp R G0 c hG0 hc t ω
      else G0 * c ^ kfun G0 c hG0 hc (R (t + 1) ω)

lemma Gp_meas {Ω : Type*} [m₀ : MeasurableSpace Ω] (𝓕 : Filtration ℕ m₀) (R : ℕ → Ω → ℝ)
    (G0 c : ℝ) (hG0 : 0 < G0) (hc : 1 < c) (hR : ∀ t, Measurable[𝓕 t] (R t)) :
    ∀ t, Measurable[𝓕 t] (Gp R G0 c hG0 hc t) := by
  intro t
  induction t with
  | zero => exact (hR 0).max measurable_const
  | succ t ih =>
    have ih' : Measurable[𝓕 (t + 1)] (Gp R G0 c hG0 hc t) := ih.mono (𝓕.mono (Nat.le_succ t)) le_rfl
    have hk : Measurable[𝓕 (t + 1)] (fun ω => G0 * c ^ kfun G0 c hG0 hc (R (t + 1) ω)) :=
      measurable_const.mul ((measurable_from_nat (f := fun k : ℕ => c ^ k)).comp
        ((kfun_meas G0 c hG0 hc).comp (hR (t + 1))))
    exact Measurable.ite (measurableSet_le (hR (t + 1)) (measurable_const.mul ih')) ih' hk

section Inv
variable {Ω : Type*} (R : ℕ → Ω → ℝ) (G0 c : ℝ) (hG0 : 0 < G0) (hc : 1 < c)

lemma Gp_ge (ω : Ω) : ∀ t, G0 ≤ Gp R G0 c hG0 hc t ω := by
  intro t
  induction t with
  | zero => exact le_max_right _ _
  | succ t ih =>
    simp only [Gp]
    split_ifs
    · exact ih
    · exact le_mul_of_one_le_right hG0.le (one_le_pow₀ hc.le)

lemma R_le_Gp (ω : Ω) : ∀ t, R t ω ≤ c * Gp R G0 c hG0 hc t ω := by
  intro t
  cases t with
  | zero =>
    simp only [Gp]
    have h1 : R 0 ω ≤ max (R 0 ω) G0 := le_max_left _ _
    have h2 : 0 ≤ max (R 0 ω) G0 := le_trans hG0.le (le_max_right _ _)
    nlinarith
  | succ t =>
    simp only [Gp]
    split_ifs with h
    · exact h
    · have hs := Nat.find_spec (exists_k G0 c (R (t + 1) ω) hG0 hc)
      have hpos : 0 ≤ G0 * c ^ kfun G0 c hG0 hc (R (t + 1) ω) := by positivity
      have : R (t + 1) ω ≤ G0 * c ^ kfun G0 c hG0 hc (R (t + 1) ω) := hs
      nlinarith

lemma Gp_stay (ω : Ω) (t : ℕ) (h : R (t + 1) ω ≤ c * Gp R G0 c hG0 hc t ω) :
    Gp R G0 c hG0 hc (t + 1) ω = Gp R G0 c hG0 hc t ω := by
  simp only [Gp, if_pos h]

lemma Gp_jump (ω : Ω) (t : ℕ) (h : c * Gp R G0 c hG0 hc t ω < R (t + 1) ω) :
    ∃ k : ℕ, Gp R G0 c hG0 hc (t + 1) ω = G0 * c ^ k ∧
      G0 * c ^ (k - 1) < R (t + 1) ω ∧ R (t + 1) ω ≤ G0 * c ^ k := by
  refine ⟨kfun G0 c hG0 hc (R (t + 1) ω), ?_, ?_, Nat.find_spec (exists_k G0 c _ hG0 hc)⟩
  · simp only [Gp, if_neg (not_le.2 h)]
  · have hGt := Gp_ge R G0 c hG0 hc ω t
    have hk0 : kfun G0 c hG0 hc (R (t + 1) ω) ≠ 0 := by
      intro h0
      have hs : R (t + 1) ω ≤ G0 * c ^ kfun G0 c hG0 hc (R (t + 1) ω) :=
        Nat.find_spec (exists_k G0 c _ hG0 hc)
      rw [h0, pow_zero, mul_one] at hs
      nlinarith
    have := Nat.find_min (exists_k G0 c (R (t + 1) ω) hG0 hc)
      (m := kfun G0 c hG0 hc (R (t + 1) ω) - 1) (by unfold kfun at hk0 ⊢; omega)
    exact lt_of_not_ge this

end Inv

end AsyncSA.Contraction.Thm1Aux

open AsyncSA.Contraction.Thm1Aux in
theorem solution {n : ℕ} {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ m₀) (alg : Algorithm n Ω)
    (h1 : alg.Assumption1 P) (h2 : alg.Assumption2 P 𝓕)
    (hx : alg.Adapted 𝓕) (h3 : alg.Assumption3 P)
    (h6 : Assumption6 alg.F) :
    ∀ᵐ ω ∂P, ∃ M : ℝ, ∀ t j, |alg.x t ω j| ≤ M := by
  obtain ⟨v, β, D, hv, hβ0, hβ1, hgr⟩ := h6
  have hn := alg.n_pos
  set alg' := scale alg v hv with halg'
  set γ : ℝ := (1 + β) / 2 with hγ
  have hγ1 : γ < 1 := by linarith
  have hβγ : β < γ := by linarith
  have hγ0 : 0 < γ := by linarith
  set ε : ℝ := 1 / γ - 1 with hε
  have hε0 : 0 < ε := by
    rw [hε, sub_pos, lt_div_iff₀ hγ0]; linarith
  have hγε : γ * (1 + ε) = 1 := by rw [hε]; field_simp; ring
  set G0 : ℝ := max 1 (D / (γ - β)) with hG0def
  have hG0 : 0 < G0 := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hc : (1:ℝ) < 1 + ε := by linarith
  -- Step 1: the scaled map satisfies the growth bound of Lemma 3
  have hF' : ∀ y : Fin n → ℝ, ∀ i, |alg'.F y i| ≤ γ * max (⨆ j, |y j|) G0 := by
    intro y i
    have hg := hgr (fun j => v j * y j)
    rw [wNorm_eq_norm hn _ _ hv, wNorm_eq_norm hn _ _ hv] at hg
    have e : (fun i => v i * y i / v i) = y := by funext i; field_simp [(hv i).ne']
    rw [e, norm_eq_iSup hn y] at hg
    have hi : |alg'.F y i| ≤ ‖fun i => alg.F (fun j => v j * y j) i / v i‖ := by
      show |alg.F (fun j => v j * y j) i / v i| ≤ _
      have := norm_le_pi_norm (fun i => alg.F (fun j => v j * y j) i / v i) i
      rw [Real.norm_eq_abs] at this
      exact this
    set r := ⨆ j, |y j| with hr
    have hr0 : 0 ≤ r := Real.iSup_nonneg fun j => abs_nonneg _
    have hD : D ≤ (γ - β) * G0 := by
      have h' : D / (γ - β) ≤ G0 := le_max_right _ _
      rw [div_le_iff₀ (by linarith)] at h'
      linarith
    calc |alg'.F y i| ≤ β * r + D := le_trans hi hg
      _ ≤ γ * max r G0 := by
        rcases le_total r G0 with h | h
        · rw [max_eq_right h]; nlinarith
        · rw [max_eq_left h]; nlinarith
  -- Step 2: the scale process G(t)
  set R : ℕ → Ω → ℝ := fun t ω => alg'.runMax t ω with hR
  have hxm' : ∀ t j, Measurable[𝓕 t] (fun ω => alg'.x t ω j) :=
    fun t j => (hx t j).div_const _
  have hRm : ∀ t, Measurable[𝓕 t] (R t) := by
    intro t
    show Measurable[𝓕 t] (alg'.runMax t)
    unfold Algorithm.runMax
    refine Measurable.iSup fun s => Measurable.iSup fun j => ?_
    exact continuous_abs.measurable.comp
      ((hxm' s j).mono (𝓕.mono (Nat.lt_succ_iff.mp s.2)) le_rfl)
  set G := Gp R G0 (1 + ε) hG0 hc with hG
  have hGm : ∀ t, Measurable[𝓕 t] (G t) := Gp_meas 𝓕 R G0 (1 + ε) hG0 hc hRm
  have hGpos : ∀ t ω, 0 < G t ω := fun t ω => lt_of_lt_of_le hG0 (Gp_ge R G0 (1 + ε) hG0 hc ω t)
  have hrun : ∀ t, Measurable[𝓕 t] (alg.runMax t) := by
    intro t
    unfold Algorithm.runMax
    refine Measurable.iSup fun s => Measurable.iSup fun j => ?_
    exact continuous_abs.measurable.comp
      ((hx s j).mono (𝓕.mono (Nat.lt_succ_iff.mp s.2)) le_rfl)
  set V : ℝ := ∑ j, v j with hVdef
  have hvV : ∀ j, v j ≤ V := fun j =>
    Finset.single_le_sum (f := v) (fun j _ => (hv j).le) (Finset.mem_univ j)
  have hV0 : 0 < V := lt_of_lt_of_le (hv ⟨0, hn⟩) (hvV _)
  have habs : ∀ t ω j, |alg.x t ω j| = v j * |alg'.x t ω j| := by
    intro t ω j
    show |alg.x t ω j| = v j * |alg.x t ω j / v j|
    rw [abs_div, abs_of_pos (hv j)]; field_simp [(hv j).ne']
  have hrunR : ∀ t ω, alg.runMax t ω ≤ V * R t ω := by
    intro t ω
    refine runMax_le alg t ω _ (mul_nonneg hV0.le (runMax_nonneg _ _ _)) fun s hs j => ?_
    have h1 := abs_le_runMax alg' ω hs j
    rw [habs]
    calc v j * |alg'.x s ω j| ≤ V * |alg'.x s ω j| :=
          mul_le_mul_of_nonneg_right (hvV j) (abs_nonneg _)
      _ ≤ V * R t ω := mul_le_mul_of_nonneg_left h1 hV0.le
  -- Step 3: Lemma 2 for the noise rescaled by v_i G(t)
  obtain ⟨cA, cB, hvar⟩ := h2.var_bound
  obtain ⟨C, hC⟩ := h3.sum_sq
  have hnoise : ∀ i, ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ → ∃ T : ℕ, ∀ t₀ t : ℕ, T ≤ t₀ → t₀ ≤ t →
      |tailW (fun s => alg.α i s ω) (fun s => 1 / (v i * G s ω) * alg.w i s ω) t₀ t| ≤ δ := by
    intro i
    have hvi := hv i
    have hh : ∀ t, Measurable[𝓕 t] (fun ω => 1 / (v i * G t ω)) :=
      fun t => measurable_const.div (measurable_const.mul (hGm t))
    have hH : ∀ t ω, |1 / (v i * G t ω)| ≤ 1 / (v i * G0) := by
      intro t ω
      have hGt := Gp_ge R G0 (1 + ε) hG0 hc ω t
      have hp : 0 < v i * G t ω := mul_pos hvi (hGpos t ω)
      rw [abs_of_pos (by positivity)]
      exact one_div_le_one_div_of_le (mul_pos hvi hG0) (mul_le_mul_of_nonneg_left hGt hvi.le)
    have hcm := fun t => cmz_mul (𝓕 t) (𝓕.le t) P (alg.w i t) (fun ω => 1 / (v i * G t ω))
      (fun ω => cA + cB * alg.runMax t ω ^ 2) ((h2.w_meas i t).mono (𝓕.le _) le_rfl) (hh t)
      (measurable_const.add (measurable_const.mul ((hrun t).pow_const 2))) _ (hH t)
      (h2.mean_zero i t) (hvar i t)
    refine lemma2 P 𝓕 (alg.α i) (fun t ω => 1 / (v i * G t ω) * alg.w i t ω)
      (fun t ω => (1 / (v i * G t ω)) ^ 2 * (cA + cB * alg.runMax t ω ^ 2)) C
      (fun t => h2.α_meas i t) ?_ ?_ (fun t => (hcm t).1) (fun t => (hcm t).2)
      (ae_of_all _ fun ω t => alg.α_mem i t ω) (h3.sum_inf i) (hC i) ?_
    · intro t
      exact ((hh t).mono (𝓕.mono (Nat.le_succ t)) le_rfl).mul (h2.w_meas i t)
    · intro t
      exact ((hh t).pow_const 2).mul
        (measurable_const.add (measurable_const.mul ((hrun t).pow_const 2)))
    · refine ae_of_all _ fun ω =>
        ⟨(1 / (v i * G0)) ^ 2 * |cA| + |cB| * (V * (1 + ε) / v i) ^ 2, fun t => ?_⟩
      set g := G t ω with hg
      set M := alg.runMax t ω with hM
      have hgpos : 0 < g := hGpos t ω
      have hM0 : 0 ≤ M := runMax_nonneg _ _ _
      have hMg : M ≤ V * (1 + ε) * g := by
        have a1 := hrunR t ω
        have a2 := R_le_Gp R G0 (1 + ε) hG0 hc ω t
        have a3 : 0 ≤ R t ω := runMax_nonneg _ _ _
        calc M ≤ V * R t ω := a1
          _ ≤ V * ((1 + ε) * g) := mul_le_mul_of_nonneg_left a2 hV0.le
          _ = _ := by ring
      have hp : 0 < v i * g := mul_pos hvi hgpos
      set hval := 1 / (v i * g) with hhval
      have hv0 : 0 < hval := by positivity
      have hv1 : hval ≤ 1 / (v i * G0) := by
        have := hH t ω; rwa [abs_of_pos hv0] at this
      have hvM : hval * M ≤ V * (1 + ε) / v i := by
        rw [hhval, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hp hvi]
        nlinarith
      have hvM0 : 0 ≤ hval * M := mul_nonneg hv0.le hM0
      calc |hval ^ 2 * (cA + cB * M ^ 2)| = hval ^ 2 * |cA + cB * M ^ 2| := by
            rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        _ ≤ hval ^ 2 * (|cA| + |cB| * M ^ 2) := by
            gcongr
            calc |cA + cB * M ^ 2| ≤ |cA| + |cB * M ^ 2| := abs_add_le _ _
              _ = |cA| + |cB| * M ^ 2 := by rw [abs_mul, abs_of_nonneg (sq_nonneg M)]
        _ = hval ^ 2 * |cA| + |cB| * (hval * M) ^ 2 := by ring
        _ ≤ (1 / (v i * G0)) ^ 2 * |cA| + |cB| * (V * (1 + ε) / v i) ^ 2 := by
            gcongr
  -- Step 4: the sample-path argument
  filter_upwards [ae_all_iff.2 hnoise] with ω hN
  by_contra hcon
  have hunb' : ¬ ∃ M : ℝ, ∀ t j, |alg'.x t ω j| ≤ M := by
    rintro ⟨M, hM⟩
    apply hcon
    refine ⟨V * M, fun t j => ?_⟩
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 j)
    rw [habs]
    calc v j * |alg'.x t ω j| ≤ v j * M := mul_le_mul_of_nonneg_left (hM t j) (hv j).le
      _ ≤ V * M := mul_le_mul_of_nonneg_right (hvV j) hM0
  have hev : ∀ᶠ t₀ in atTop, ∀ i, ∀ t, t₀ ≤ t →
      |tailW (fun s => alg.α i s ω) (fun s => 1 / (v i * G s ω) * alg.w i s ω) t₀ t| ≤ ε :=
    eventually_all.2 fun i => by
      obtain ⟨T, hT⟩ := hN i ε hε0
      exact eventually_atTop.2 ⟨T, fun t₀ h t ht => hT t₀ t h ht⟩
  obtain ⟨T, hT⟩ := eventually_atTop.1 hev
  -- bounded iterates from a time after which G is constant
  have hbound_of_const : ∀ t₀ : ℕ, (∀ k, G (t₀ + k) ω = G t₀ ω) →
      ∃ M : ℝ, ∀ t j, |alg'.x t ω j| ≤ M := by
    intro t₀ hconst
    refine ⟨R t₀ ω + (1 + ε) * G t₀ ω, fun t j => ?_⟩
    have h1 := abs_le_runMax alg' ω (le_refl t) j
    have hG0' : 0 ≤ (1 + ε) * G t₀ ω := by have := hGpos t₀ ω; positivity
    rcases le_or_gt t t₀ with h | h
    · have := runMax_mono alg' ω h
      show |alg'.x t ω j| ≤ alg'.runMax t₀ ω + (1 + ε) * G t₀ ω
      linarith
    · obtain ⟨k, rfl⟩ : ∃ k, t = t₀ + k := ⟨t - t₀, by omega⟩
      have h2 := R_le_Gp R G0 (1 + ε) hG0 hc ω (t₀ + k)
      have h3 : 0 ≤ R t₀ ω := runMax_nonneg _ _ _
      have h4 : Gp R G0 (1 + ε) hG0 hc (t₀ + k) ω = G t₀ ω := hconst k
      rw [h4] at h2
      show |alg'.x (t₀ + k) ω j| ≤ R t₀ ω + (1 + ε) * G t₀ ω
      have : |alg'.x (t₀ + k) ω j| ≤ R (t₀ + k) ω := h1
      linarith
  have hjump : ∃ t ≥ T, (1 + ε) * G t ω < R (t + 1) ω := by
    by_contra hno
    simp only [not_exists, not_and, not_lt] at hno
    apply hunb'
    refine hbound_of_const T fun k => ?_
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [← add_assoc]
      have := Gp_stay R G0 (1 + ε) hG0 hc ω (T + k) (hno _ (by omega))
      rw [← ih]
      exact this
  obtain ⟨t, htT, hjt⟩ := hjump
  obtain ⟨k, hk1, hk2, hk3⟩ := Gp_jump R G0 (1 + ε) hG0 hc ω t hjt
  have hM₀ : alg'.runMax (t + 1) ω ≤ G (t + 1) ω := by
    have : G (t + 1) ω = G0 * (1 + ε) ^ k := hk1
    rw [this]; exact hk3
  have hWeq : ∀ i, (fun s => alg'.w i s ω / G s ω) =
      (fun s => 1 / (v i * G s ω) * alg.w i s ω) := by
    intro i; funext s
    show alg.w i s ω / v i / G s ω = _
    have := hGpos s ω
    field_simp [(hv i).ne']
  have L3 := lemma3 alg' ω γ G0 ε (fun s => G s ω) (t + 1) ⟨hγ0.le, hγ1⟩ hG0 hε0 hγε hF'
    rfl (fun s hs => Gp_stay R G0 (1 + ε) hG0 hc ω s hs)
    (fun s hs => Gp_jump R G0 (1 + ε) hG0 hc ω s hs) hM₀
    (fun s hs i => by
      rw [hWeq i]
      exact hT (t + 1) (by omega) i s hs) hunb'
  apply hunb'
  refine hbound_of_const (t + 1) fun k => (L3 (t + 1 + k) (by omega)).1
