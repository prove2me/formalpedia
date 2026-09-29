-- Prove2me | solution 1 for AutomorphicForm.apply_scalar_eq_zero_of_conj_unitary_eq_of_forall_integral_upperTriangular_complex_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/77792840-6a5d-5de5-9479-7012c8fc1c52

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_apply_scalar_eq_zero_of_conj_unitary_eq_of_forall_integral_upperTriangular_complex_eq_zero

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open MeasureTheory Filter Topology

noncomputable section

namespace P2mHCLimitC

section SecondDiff

variable {g g' g'' : ℝ → ℂ}

theorem sd_eq_integral (hg : ∀ s, HasDerivAt g (g' s) s) (hg' : ∀ s, HasDerivAt g' (g'' s) s)
    (hcont : Continuous g'') (s : ℝ) :
    g s + g (-s) - 2 * g 0 = ∫ t in (0 : ℝ)..s, ∫ u in (-t)..t, g'' u := by
  have hg'c : Continuous g' := continuous_iff_continuousAt.2 fun s => (hg' s).continuousAt
  have hin : ∀ t, ∫ u in (-t)..t, g'' u = g' t - g' (-t) := fun t =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hg' u) (hcont.intervalIntegrable _ _)
  simp_rw [hin]
  have hder : ∀ t, HasDerivAt (fun t => g t + g (-t)) (g' t - g' (-t)) t := by
    intro t
    have h2 : HasDerivAt (fun t : ℝ => g (-t)) (-(g' (-t))) t := by
      have := (hg (-t)).scomp t (hasDerivAt_neg t)
      simp at this
      exact this
    exact ((hg t).add h2).congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t)
    ((hg'c.sub (hg'c.comp continuous_neg)).intervalIntegrable _ _)]
  simp only [neg_zero]
  ring_nf

theorem abs_le_of_mem_uIoc_neg {u t : ℝ} (hu : u ∈ Set.uIoc (-t) t) : |u| ≤ |t| := by
  rw [Set.mem_uIoc] at hu
  rw [abs_le]
  rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have ht : 0 ≤ t := by linarith
    rw [abs_of_nonneg ht]
    exact ⟨h1.le, h2⟩
  · have ht : t ≤ 0 := by linarith
    rw [abs_of_nonpos ht]
    exact ⟨by linarith, by linarith⟩

theorem abs_le_of_mem_uIoc_zero {t s : ℝ} (ht : t ∈ Set.uIoc 0 s) : |t| ≤ |s| := by
  rw [Set.mem_uIoc] at ht
  rw [abs_le]
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hs : 0 ≤ s := by linarith
    rw [abs_of_nonneg hs]
    exact ⟨by linarith, h2⟩
  · have hs : s ≤ 0 := by linarith
    rw [abs_of_nonpos hs]
    exact ⟨by linarith, by linarith⟩

theorem norm_sd_le (hg : ∀ s, HasDerivAt g (g' s) s) (hg' : ∀ s, HasDerivAt g' (g'' s) s)
    (hcont : Continuous g'') {s M : ℝ} (hM : ∀ u, |u| ≤ |s| → ‖g'' u‖ ≤ M) :
    ‖g s + g (-s) - 2 * g 0‖ ≤ 2 * M * s ^ 2 := by
  rw [sd_eq_integral hg hg' hcont s]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp))
  have inner : ∀ t ∈ Set.uIoc 0 s, ‖∫ u in (-t)..t, g'' u‖ ≤ 2 * M * |s| := by
    intro t ht
    have ht' : |t| ≤ |s| := abs_le_of_mem_uIoc_zero ht
    calc ‖∫ u in (-t)..t, g'' u‖ ≤ M * |t - -t| :=
          intervalIntegral.norm_integral_le_of_norm_le_const fun u hu =>
            hM u ((abs_le_of_mem_uIoc_neg hu).trans ht')
      _ = 2 * M * |t| := by
          rw [sub_neg_eq_add, ← two_mul, abs_mul, abs_two]
          ring
      _ ≤ 2 * M * |s| := by gcongr
  calc ‖∫ t in (0 : ℝ)..s, ∫ u in (-t)..t, g'' u‖ ≤ 2 * M * |s| * |s - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const inner
    _ = 2 * M * s ^ 2 := by rw [sub_zero, ← sq_abs s]; ring

theorem tendsto_sd_div_sq (hg : ∀ s, HasDerivAt g (g' s) s) (hg' : ∀ s, HasDerivAt g' (g'' s) s)
    (hcont : Continuous g'') :
    Tendsto (fun s : ℝ => (s ^ 2)⁻¹ • (g s + g (-s) - 2 * g 0)) (𝓝[≠] 0) (𝓝 (g'' 0)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuous_iff.1 hcont 0 (ε / 4) (by positivity)
  refine ⟨δ, hδ, fun s hs hsδ => ?_⟩
  have hs0 : s ≠ 0 := hs
  rw [dist_zero_right, Real.norm_eq_abs] at hsδ

  set C : ℂ := g'' 0 with hC
  set k : ℝ → ℂ := fun s => g s - (s ^ 2 / 2) • C with hk
  set k' : ℝ → ℂ := fun s => g' s - s • C with hk'
  set k'' : ℝ → ℂ := fun s => g'' s - C with hk''
  have hk1 : ∀ s, HasDerivAt k (k' s) s := by
    intro s
    have hp : HasDerivAt (fun s : ℝ => (s ^ 2 / 2) • C) (s • C) s := by
      have h1 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) s s := by
        convert (hasDerivAt_pow 2 s).div_const 2 using 1
        · rfl
        · rfl
        ring
      exact h1.smul_const C
    exact (hg s).sub hp
  have hk2 : ∀ s, HasDerivAt k' (k'' s) s := by
    intro s
    have hp : HasDerivAt (fun s : ℝ => s • C) C s := by
      simpa using (hasDerivAt_id s).smul_const C
    exact (hg' s).sub hp
  have hk''c : Continuous k'' := hcont.sub continuous_const
  have hbound : ∀ u, |u| ≤ |s| → ‖k'' u‖ ≤ ε / 4 := by
    intro u hu
    have hu' : dist u 0 < δ := by
      rw [dist_zero_right, Real.norm_eq_abs]
      exact lt_of_le_of_lt hu hsδ
    have := hδ' u hu'
    rw [dist_eq_norm] at this
    exact this.le
  have hsd := norm_sd_le hk1 hk2 hk''c hbound
  have hkey : k s + k (-s) - 2 * k 0 = (g s + g (-s) - 2 * g 0) - (s ^ 2 : ℝ) • C := by
    simp only [hk, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_pow]
    push_cast
    ring
  rw [hkey] at hsd
  rw [dist_eq_norm]
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hcalc : (s ^ 2)⁻¹ • ((g s + g (-s) - 2 * g 0) - (s ^ 2 : ℝ) • C) =
      (s ^ 2)⁻¹ • (g s + g (-s) - 2 * g 0) - C := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hs2.ne', one_smul]
  rw [← hcalc, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hs2]
  calc (s ^ 2)⁻¹ * ‖g s + g (-s) - 2 * g 0 - (s ^ 2 : ℝ) • C‖ ≤ (s ^ 2)⁻¹ * (2 * (ε / 4) * s ^ 2) := by
        gcongr
    _ = ε / 2 := by field_simp; ring
    _ < ε := by linarith

end SecondDiff

section Interchange

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_secondDeriv_eq_zero (G G₁ G₂ : ℝ → Ω → ℂ)
    (hG : ∀ s ω, HasDerivAt (fun s => G s ω) (G₁ s ω) s)
    (hG₁ : ∀ s ω, HasDerivAt (fun s => G₁ s ω) (G₂ s ω) s)
    (hG₂c : ∀ ω, Continuous fun s => G₂ s ω)
    (hint : ∀ s, Integrable (G s) μ)
    (hmeas : AEStronglyMeasurable (G₂ 0) μ)
    (bound₀ bound₂ : Ω → ℝ) (hb₀ : Integrable bound₀ μ) (hb₂ : Integrable bound₂ μ)
    (hGb : ∀ s ω, |s| ≤ 1 → ‖G s ω‖ ≤ bound₀ ω)
    (hG₂b : ∀ s ω, |s| ≤ 1 → ‖G₂ s ω‖ ≤ bound₂ ω)
    {ε : ℝ} (hε : 0 < ε) (hvan : ∀ s : ℝ, s ≠ 0 → |s| < ε → ∫ ω, G s ω ∂μ = 0) :
    ∫ ω, G₂ 0 ω ∂μ = 0 := by

  have hmem : {s : ℝ | s ≠ 0 ∧ |s| < min ε 1} ∈ 𝓝[≠] (0 : ℝ) := by
    have h1 : {s : ℝ | |s| < min ε 1} ∈ 𝓝 (0 : ℝ) := by
      have : Metric.ball (0 : ℝ) (min ε 1) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 (lt_min hε one_pos)
      refine Filter.mem_of_superset this fun s hs => ?_
      simpa [Metric.mem_ball, dist_zero_right] using hs
    have h2 := inter_mem_nhdsWithin ({0}ᶜ : Set ℝ) h1
    refine Filter.mem_of_superset h2 ?_
    rintro s ⟨hs1, hs2⟩
    exact ⟨hs1, hs2⟩

  have hcont : ContinuousAt (fun s => ∫ ω, G s ω ∂μ) 0 := by
    refine continuousAt_of_dominated (bound := bound₀) ?_ ?_ hb₀ ?_
    · exact Filter.Eventually.of_forall fun s => (hint s).aestronglyMeasurable
    · have : Metric.ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 one_pos
      refine Filter.eventually_of_mem this fun s hs => Filter.Eventually.of_forall fun ω => hGb s ω ?_
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
      exact hs.le
    · exact Filter.Eventually.of_forall fun ω => (hG 0 ω).continuousAt
  have h0 : ∫ ω, G 0 ω ∂μ = 0 := by
    have t1 : Tendsto (fun s => ∫ ω, G s ω ∂μ) (𝓝[≠] 0) (𝓝 (∫ ω, G 0 ω ∂μ)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have t2 : Tendsto (fun s => ∫ ω, G s ω ∂μ) (𝓝[≠] 0) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      refine Filter.eventuallyEq_of_mem hmem fun s hs => ?_
      exact (hvan s hs.1 (lt_of_lt_of_le hs.2 (min_le_left _ _))).symm
    exact tendsto_nhds_unique t1 t2

  set SD : ℝ → Ω → ℂ := fun s ω => (s ^ 2)⁻¹ • (G s ω + G (-s) ω - 2 * G 0 ω) with hSD
  have hSDint : ∀ s, s ≠ 0 → |s| < ε → ∫ ω, SD s ω ∂μ = 0 := by
    intro s hs hsε
    have e1 : ∫ ω, (G s ω + G (-s) ω - 2 * G 0 ω) ∂μ = 0 := by
      have i1 : Integrable (fun ω => G s ω + G (-s) ω) μ := (hint s).add (hint (-s))
      have i2 : Integrable (fun ω => 2 * G 0 ω) μ := (hint 0).const_mul 2
      rw [integral_sub i1 i2, integral_add (hint s) (hint (-s)), integral_const_mul, hvan s hs hsε,
        hvan (-s) (neg_ne_zero.2 hs) (by rwa [abs_neg]), h0]
      ring
    simp only [hSD]
    rw [integral_smul, e1, smul_zero]

  have hlim : Tendsto (fun s => ∫ ω, SD s ω ∂μ) (𝓝[≠] 0) (𝓝 (∫ ω, G₂ 0 ω ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun ω => 2 * bound₂ ω) ?_ ?_ (hb₂.const_mul 2) ?_
    · refine Filter.Eventually.of_forall fun s => ?_
      exact (((hint s).add (hint (-s))).sub ((hint 0).const_mul 2)).aestronglyMeasurable.const_smul ((s ^ 2)⁻¹ : ℝ)
    · refine Filter.eventually_of_mem hmem fun s hs => Filter.Eventually.of_forall fun ω => ?_
      have hs1 : |s| ≤ 1 := (lt_of_lt_of_le hs.2 (min_le_right _ _)).le
      have hb : ∀ u, |u| ≤ |s| → ‖G₂ u ω‖ ≤ bound₂ ω := fun u hu => hG₂b u ω (hu.trans hs1)
      have := norm_sd_le (fun u => hG u ω) (fun u => hG₁ u ω) (hG₂c ω) hb
      have hs0 : s ≠ 0 := hs.1
      have hs2 : (0 : ℝ) < s ^ 2 := by positivity
      simp only [hSD]
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hs2]
      calc (s ^ 2)⁻¹ * ‖G s ω + G (-s) ω - 2 * G 0 ω‖ ≤ (s ^ 2)⁻¹ * (2 * bound₂ ω * s ^ 2) := by gcongr
        _ = 2 * bound₂ ω := by field_simp
    · exact Filter.Eventually.of_forall fun ω =>
        tendsto_sd_div_sq (fun u => hG u ω) (fun u => hG₁ u ω) (hG₂c ω)
  have hlim0 : Tendsto (fun s => ∫ ω, SD s ω ∂μ) (𝓝[≠] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    refine Filter.eventuallyEq_of_mem hmem fun s hs => ?_
    exact (hSDint s hs.1 (lt_of_lt_of_le hs.2 (min_le_left _ _))).symm
  exact tendsto_nhds_unique hlim hlim0

end Interchange

abbrev Ent : Type := Fin 2 → Fin 2 → ℂ

def mk (a b c d : ℂ) : Ent := Matrix.of.symm !![a, b; c, d]

@[scoped simp] theorem mk_apply₀₀ (a b c d : ℂ) : mk a b c d 0 0 = a := rfl
@[scoped simp] theorem mk_apply₀₁ (a b c d : ℂ) : mk a b c d 0 1 = b := rfl
@[scoped simp] theorem mk_apply₁₀ (a b c d : ℂ) : mk a b c d 1 0 = c := rfl
@[scoped simp] theorem mk_apply₁₁ (a b c d : ℂ) : mk a b c d 1 1 = d := rfl

theorem ent_eq_mk (Y : Ent) : Y = mk (Y 0 0) (Y 0 1) (Y 1 0) (Y 1 1) := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem mk_eq_mk_iff {a b c d a' b' c' d' : ℂ} :
    mk a b c d = mk a' b' c' d' ↔ a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  constructor
  · intro h
    exact ⟨by simpa using congrFun (congrFun h 0) 0, by simpa using congrFun (congrFun h 0) 1,
      by simpa using congrFun (congrFun h 1) 0, by simpa using congrFun (congrFun h 1) 1⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

theorem mk_add (a b c d a' b' c' d' : ℂ) :
    mk a b c d + mk a' b' c' d' = mk (a + a') (b + b') (c + c') (d + d') := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem smul_mk (z a b c d : ℂ) : z • mk a b c d = mk (z * a) (z * b) (z * c) (z * d) := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem real_smul_mk (r : ℝ) (a b c d : ℂ) :
    r • mk a b c d = mk (r * a) (r * b) (r * c) (r * d) := by
  rw [← Complex.coe_smul, smul_mk]

theorem neg_mk (a b c d : ℂ) : -mk a b c d = mk (-a) (-b) (-c) (-d) := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem entry_norm_le (Y : Ent) (i j : Fin 2) : ‖Y i j‖ ≤ ‖Y‖ :=
  (norm_le_pi_norm (Y i) j).trans (norm_le_pi_norm Y i)

theorem norm_le_of_entries (Y : Ent) {B : ℝ} (hB : 0 ≤ B) (h : ∀ i j, ‖Y i j‖ ≤ B) : ‖Y‖ ≤ B :=
  (pi_norm_le_iff_of_nonneg hB).2 fun i => (pi_norm_le_iff_of_nonneg hB).2 fun j => h i j

theorem norm_mk_le {a b c d : ℂ} {B : ℝ} (hB : 0 ≤ B) (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ B)
    (hd : ‖d‖ ≤ B) : ‖mk a b c d‖ ≤ B := by
  refine norm_le_of_entries _ hB fun i j => ?_
  fin_cases i <;> fin_cases j <;> assumption

def Dg : Ent := mk 1 0 0 (-1)
def E12 : Ent := mk 0 1 0 0
def E21 : Ent := mk 0 0 1 0
def One : Ent := mk 1 0 0 1

def pt (c v : ℂ) : Ent := mk c v 0 c

def Bm (c w v : ℂ) : Ent := mk (c * Complex.exp w) v 0 (c * Complex.exp (-w))

theorem Bm_zero (c v : ℂ) : Bm c 0 v = pt c v := by
  simp [Bm, pt]

theorem pt_eq (c v : ℂ) : pt c v = pt c 0 + v • E12 := by
  rw [pt, pt, E12, smul_mk, mk_add, mk_eq_mk_iff]
  simp

theorem norm_v_le_pt (c v : ℂ) : ‖v‖ ≤ ‖pt c v‖ := by
  simpa [pt] using entry_norm_le (pt c v) 0 1

theorem norm_v_le_Bm (c w v : ℂ) : ‖v‖ ≤ ‖Bm c w v‖ := by
  simpa [Bm] using entry_norm_le (Bm c w v) 0 1

theorem hasDerivAt_mk {a b c d : ℝ → ℂ} {a' b' c' d' : ℂ} {s : ℝ}
    (ha : HasDerivAt a a' s) (hb : HasDerivAt b b' s) (hc : HasDerivAt c c' s) (hd : HasDerivAt d d' s) :
    HasDerivAt (fun s => mk (a s) (b s) (c s) (d s)) (mk a' b' c' d') s := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j
  · simpa using ha
  · simpa using hb
  · simpa using hc
  · simpa using hd

theorem continuous_mk {X : Type} [TopologicalSpace X] {a b c d : X → ℂ} (ha : Continuous a)
    (hb : Continuous b) (hc : Continuous c) (hd : Continuous d) :
    Continuous fun x => mk (a x) (b x) (c x) (d x) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j
  · simpa using ha
  · simpa using hb
  · simpa using hc
  · simpa using hd

section ChainRule

variable {F : Ent → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)

include hF

theorem contDiff_fderiv' : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ F) := (contDiff_infty_iff_fderiv.1 hF).2

theorem contDiff_fderiv₂ : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fderiv ℝ F)) :=
  (contDiff_infty_iff_fderiv.1 (contDiff_fderiv' hF)).2

theorem hasDerivAt_comp_curve {γ γ' : ℝ → Ent} (hγ : ∀ s, HasDerivAt γ (γ' s) s) (s : ℝ) :
    HasDerivAt (fun s => F (γ s)) (fderiv ℝ F (γ s) (γ' s)) s :=
  ((hF.differentiable (by simp)) (γ s)).hasFDerivAt.comp_hasDerivAt s (hγ s)

theorem hasDerivAt_fderiv_comp_curve {γ γ' : ℝ → Ent} (hγ : ∀ s, HasDerivAt γ (γ' s) s) {s : ℝ} {W : Ent}
    (hγ' : HasDerivAt γ' W s) :
    HasDerivAt (fun s => fderiv ℝ F (γ s) (γ' s))
      (fderiv ℝ (fderiv ℝ F) (γ s) (γ' s) (γ' s) + fderiv ℝ F (γ s) W) s := by
  have h1 : HasDerivAt (fun s => fderiv ℝ F (γ s)) (fderiv ℝ (fderiv ℝ F) (γ s) (γ' s)) s :=
    (((contDiff_fderiv' hF).differentiable (by simp)) (γ s)).hasFDerivAt.comp_hasDerivAt s (hγ s)
  exact h1.clm_apply hγ'

theorem second_order_eq_zero_of_const {γ γ' : ℝ → Ent} (hγ : ∀ s, HasDerivAt γ (γ' s) s)
    {p₀ V W : Ent} (h0 : γ 0 = p₀) (h0' : γ' 0 = V) (hγ' : HasDerivAt γ' W 0)
    (hconst : ∀ s, F (γ s) = F p₀) :
    fderiv ℝ (fderiv ℝ F) p₀ V V + fderiv ℝ F p₀ W = 0 := by
  have h1 : ∀ s, fderiv ℝ F (γ s) (γ' s) = 0 := fun s => by
    have hc : HasDerivAt (fun s => F (γ s)) 0 s := by
      simp_rw [hconst]
      exact hasDerivAt_const _ _
    exact (hasDerivAt_comp_curve hF hγ s).unique hc
  have h2 := hasDerivAt_fderiv_comp_curve hF hγ hγ'
  rw [h0, h0'] at h2
  have h3 : HasDerivAt (fun s => fderiv ℝ F (γ s) (γ' s)) 0 0 := by
    simp_rw [h1]
    exact hasDerivAt_const _ _
  exact h2.unique h3

end ChainRule

section Unitary

open ComplexConjugate

def uMat (β : ℂ) (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos s : ℂ), β * Real.sin s; -(conj β * Real.sin s), (Real.cos s : ℂ)]

@[scoped simp] theorem uMat_apply₀₀ (β : ℂ) (s : ℝ) : uMat β s 0 0 = Real.cos s := rfl
@[scoped simp] theorem uMat_apply₀₁ (β : ℂ) (s : ℝ) : uMat β s 0 1 = β * Real.sin s := rfl
@[scoped simp] theorem uMat_apply₁₀ (β : ℂ) (s : ℝ) : uMat β s 1 0 = -(conj β * Real.sin s) := rfl
@[scoped simp] theorem uMat_apply₁₁ (β : ℂ) (s : ℝ) : uMat β s 1 1 = Real.cos s := rfl
@[scoped simp] theorem of_pt_apply (c v : ℂ) (i j : Fin 2) : Matrix.of (pt c v) i j = pt c v i j := rfl
@[scoped simp] theorem pt_apply₀₀ (c v : ℂ) : pt c v 0 0 = c := rfl
@[scoped simp] theorem pt_apply₀₁ (c v : ℂ) : pt c v 0 1 = v := rfl
@[scoped simp] theorem pt_apply₁₀ (c v : ℂ) : pt c v 1 0 = 0 := rfl
@[scoped simp] theorem pt_apply₁₁ (c v : ℂ) : pt c v 1 1 = c := rfl

theorem cos_sq_add_sin_sq_complex (s : ℝ) : (Real.cos s : ℂ) ^ 2 + (Real.sin s : ℂ) ^ 2 = 1 := by
  exact_mod_cast Real.cos_sq_add_sin_sq s

theorem uMat_mem_unitaryGroup {β : ℂ} (hβ : conj β * β = 1) (s : ℝ) :
    uMat β s ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hc := cos_sq_add_sin_sq_complex s
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Matrix.one_apply, -Complex.ofReal_cos, -Complex.ofReal_sin]
  · linear_combination hc + (Real.sin s : ℂ) ^ 2 * hβ
  · ring
  · ring
  · linear_combination hc + (Real.sin s : ℂ) ^ 2 * hβ

def Pc (β c v : ℂ) (s : ℝ) : Ent :=
  mk (c + v * conj β * ((Real.sin s * Real.cos s : ℝ) : ℂ)) (v * ((Real.cos s ^ 2 : ℝ) : ℂ))
    (-(v * conj β ^ 2 * ((Real.sin s ^ 2 : ℝ) : ℂ))) (c - v * conj β * ((Real.sin s * Real.cos s : ℝ) : ℂ))

theorem conj_pt_eq_Pc {β : ℂ} (hβ : conj β * β = 1) (c v : ℂ) (s : ℝ) :
    Matrix.of.symm (uMat β s * Matrix.of (pt c v) * star (uMat β s)) = Pc β c v s := by
  have hc := cos_sq_add_sin_sq_complex s
  rw [Pc, ent_eq_mk (Matrix.of.symm _), mk_eq_mk_iff]
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, uMat_apply₀₀, uMat_apply₀₁, uMat_apply₁₀, uMat_apply₁₁, of_pt_apply,
    pt_apply₀₀, pt_apply₀₁, pt_apply₁₀, pt_apply₁₁, Complex.star_def, map_mul, map_neg, Complex.conj_ofReal,
    Complex.conj_conj, Complex.ofReal_mul, Complex.ofReal_pow]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination c * hc + c * (Real.sin s : ℂ) ^ 2 * hβ
  · ring
  · ring
  · linear_combination c * hc + c * (Real.sin s : ℂ) ^ 2 * hβ

theorem Pc_zero (β c v : ℂ) : Pc β c v 0 = pt c v := by
  rw [Pc, pt, mk_eq_mk_iff]
  simp

def Pc' (β v : ℂ) (s : ℝ) : Ent :=
  mk (v * conj β * ((Real.cos s ^ 2 - Real.sin s ^ 2 : ℝ) : ℂ)) (v * ((-(2 * Real.sin s * Real.cos s) : ℝ) : ℂ))
    (-(v * conj β ^ 2 * ((2 * Real.sin s * Real.cos s : ℝ) : ℂ)))
    (-(v * conj β * ((Real.cos s ^ 2 - Real.sin s ^ 2 : ℝ) : ℂ)))

def Pc''₀ (β v : ℂ) : Ent := (-(2 * v)) • E12 + (-(2 * v * conj β ^ 2)) • E21

theorem hasDerivAt_sin_mul_cos (s : ℝ) :
    HasDerivAt (fun s => Real.sin s * Real.cos s) (Real.cos s ^ 2 - Real.sin s ^ 2) s := by
  have := (Real.hasDerivAt_sin s).mul (Real.hasDerivAt_cos s)
  convert this using 1
  · rfl
  · rfl
  · rfl
  ring

theorem hasDerivAt_cos_sq (s : ℝ) : HasDerivAt (fun s => Real.cos s ^ 2) (-(2 * Real.sin s * Real.cos s)) s := by
  have := (Real.hasDerivAt_cos s).pow 2
  convert this using 1
  · rfl
  · rfl
  · rfl
  ring

theorem hasDerivAt_sin_sq (s : ℝ) : HasDerivAt (fun s => Real.sin s ^ 2) (2 * Real.sin s * Real.cos s) s := by
  have := (Real.hasDerivAt_sin s).pow 2
  convert this using 1
  · rfl
  · rfl
  · rfl
  ring

theorem hasDerivAt_cos_sq_sub_sin_sq (s : ℝ) :
    HasDerivAt (fun s => Real.cos s ^ 2 - Real.sin s ^ 2) (-(4 * Real.sin s * Real.cos s)) s := by
  have := (hasDerivAt_cos_sq s).fun_sub (hasDerivAt_sin_sq s)
  convert this using 1 <;> first | rfl | ring1 | (funext _; ring1)

theorem hasDerivAt_two_sin_cos (s : ℝ) :
    HasDerivAt (fun s => 2 * Real.sin s * Real.cos s) (2 * (Real.cos s ^ 2 - Real.sin s ^ 2)) s := by
  have := (hasDerivAt_sin_mul_cos s).const_mul 2
  convert this using 1 <;> first | rfl | ring1 | (funext _; ring1)

theorem hasDerivAt_Pc (β c v : ℂ) (s : ℝ) : HasDerivAt (Pc β c v) (Pc' β v s) s := by
  unfold Pc Pc'
  refine hasDerivAt_mk ?_ ?_ ?_ ?_
  · simpa using ((hasDerivAt_sin_mul_cos s).ofReal_comp.const_mul (v * conj β)).const_add c
  · exact (hasDerivAt_cos_sq s).ofReal_comp.const_mul v
  · exact ((hasDerivAt_sin_sq s).ofReal_comp.const_mul (v * conj β ^ 2)).neg
  · have := ((hasDerivAt_sin_mul_cos s).ofReal_comp.const_mul (v * conj β)).const_sub c
    simpa using this

theorem hasDerivAt_Pc'_zero (β v : ℂ) : HasDerivAt (Pc' β v) (Pc''₀ β v) 0 := by
  have h : HasDerivAt (Pc' β v)
      (mk (v * conj β * ((-(4 * Real.sin 0 * Real.cos 0) : ℝ) : ℂ))
        (v * ((-(2 * (Real.cos 0 ^ 2 - Real.sin 0 ^ 2)) : ℝ) : ℂ))
        (-(v * conj β ^ 2 * ((2 * (Real.cos 0 ^ 2 - Real.sin 0 ^ 2) : ℝ) : ℂ)))
        (-(v * conj β * ((-(4 * Real.sin 0 * Real.cos 0) : ℝ) : ℂ)))) 0 := by
    unfold Pc'
    refine hasDerivAt_mk ?_ ?_ ?_ ?_
    · exact (hasDerivAt_cos_sq_sub_sin_sq 0).ofReal_comp.const_mul (v * conj β)
    · exact (hasDerivAt_two_sin_cos 0).neg.ofReal_comp.const_mul v
    · exact ((hasDerivAt_two_sin_cos 0).ofReal_comp.const_mul (v * conj β ^ 2)).neg
    · exact ((hasDerivAt_cos_sq_sub_sin_sq 0).ofReal_comp.const_mul (v * conj β)).neg
  convert h using 1
  rw [Pc''₀, E12, E21, smul_mk, smul_mk, mk_add, mk_eq_mk_iff]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> ring

theorem Pc'_zero (β v : ℂ) : Pc' β v 0 = (v * conj β) • Dg := by
  rw [Pc', Dg, smul_mk, mk_eq_mk_iff]
  simp

variable {F : Ent → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
  (hinv : ∀ u : Matrix (Fin 2) (Fin 2) ℂ, u ∈ Matrix.unitaryGroup (Fin 2) ℂ →
    ∀ E : Ent, F (Matrix.of.symm (u * Matrix.of E * star u)) = F E)

include hF hinv

theorem second_order_unitary {β : ℂ} (hβ : conj β * β = 1) (c v : ℂ) :
    fderiv ℝ (fderiv ℝ F) (pt c v) ((v * conj β) • Dg) ((v * conj β) • Dg) +
      fderiv ℝ F (pt c v) (Pc''₀ β v) = 0 :=
  second_order_eq_zero_of_const hF (hasDerivAt_Pc β c v) (Pc_zero β c v) (Pc'_zero β v)
    (hasDerivAt_Pc'_zero β v) fun s => by rw [← conj_pt_eq_Pc hβ, hinv _ (uMat_mem_unitaryGroup hβ s)]

theorem pointwise_identity (c : ℂ) {v : ℂ} (hv : v ≠ 0) :
    (‖v‖ ^ 2 : ℝ) • (fderiv ℝ (fderiv ℝ F) (pt c v) Dg Dg +
        fderiv ℝ (fderiv ℝ F) (pt c v) (Complex.I • Dg) (Complex.I • Dg)) =
      (4 : ℝ) • fderiv ℝ F (pt c v) (v • E12) := by
  have hn : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hv)
  have hvv : v * conj v = ((‖v‖ : ℂ)) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring

  set β₁ : ℂ := v / (‖v‖ : ℂ) with hβ₁
  set β₂ : ℂ := -Complex.I * v / (‖v‖ : ℂ) with hβ₂
  have hcβ₁ : conj β₁ = conj v / (‖v‖ : ℂ) := by
    rw [hβ₁, map_div₀, Complex.conj_ofReal]
  have hcβ₂ : conj β₂ = Complex.I * conj v / (‖v‖ : ℂ) := by
    rw [hβ₂, map_div₀, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hu₁ : conj β₁ * β₁ = 1 := by
    rw [hcβ₁, hβ₁]
    field_simp
    linear_combination hvv
  have hu₂ : conj β₂ * β₂ = 1 := by
    rw [hcβ₂, hβ₂]
    field_simp
    linear_combination hvv - (v * conj v) * Complex.I_sq
  have hl₁ : v * conj β₁ = (‖v‖ : ℂ) := by
    rw [hcβ₁]
    field_simp
    linear_combination hvv
  have hl₂ : v * conj β₂ = Complex.I * (‖v‖ : ℂ) := by
    rw [hcβ₂]
    field_simp
    linear_combination hvv
  have hsq : conj β₂ ^ 2 = -(conj β₁ ^ 2) := by
    rw [hcβ₁, hcβ₂]
    field_simp
    linear_combination conj v ^ 2 * Complex.I_sq
  have e₁ := second_order_unitary hF hinv hu₁ c v
  have e₂ := second_order_unitary hF hinv hu₂ c v
  rw [hl₁] at e₁
  rw [hl₂] at e₂
  simp only [Pc''₀] at e₁ e₂
  rw [hsq] at e₂

  have hs₁ : ((‖v‖ : ℂ)) • Dg = (‖v‖ : ℝ) • Dg := Complex.coe_smul _ _
  have hs₂ : (Complex.I * (‖v‖ : ℂ)) • Dg = (‖v‖ : ℝ) • (Complex.I • Dg) := by
    rw [mul_comm, mul_smul, Complex.coe_smul]
  rw [hs₁] at e₁
  rw [hs₂] at e₂
  set Q := fderiv ℝ (fderiv ℝ F) (pt c v) with hQ
  set L := fderiv ℝ F (pt c v) with hL
  have key : (‖v‖ ^ 2 : ℝ) • (Q Dg Dg + Q (Complex.I • Dg) (Complex.I • Dg)) +
      L ((-(2 * v)) • E12 + (-(2 * v * conj β₁ ^ 2)) • E21 +
        ((-(2 * v)) • E12 + (-(2 * v * -conj β₁ ^ 2)) • E21)) = 0 := by
    have : (‖v‖ ^ 2 : ℝ) • (Q Dg Dg + Q (Complex.I • Dg) (Complex.I • Dg)) =
        Q ((‖v‖ : ℝ) • Dg) ((‖v‖ : ℝ) • Dg) + Q ((‖v‖ : ℝ) • (Complex.I • Dg)) ((‖v‖ : ℝ) • (Complex.I • Dg)) := by
      simp only [map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_smul, smul_add, sq]
    rw [this, map_add L]
    linear_combination e₁ + e₂
  have hE : (-(2 * v)) • E12 + (-(2 * v * conj β₁ ^ 2)) • E21 +
      ((-(2 * v)) • E12 + (-(2 * v * -conj β₁ ^ 2)) • E21) = -((4 : ℝ) • (v • E12)) := by
    simp only [E12, E21, smul_mk, mk_add, real_smul_mk, neg_mk, mk_eq_mk_iff]
    push_cast
    exact ⟨by ring, by ring, by ring, by ring⟩
  rw [hE, map_neg, map_smul L (4 : ℝ) (v • E12)] at key
  simp only [Complex.real_smul] at key ⊢
  linear_combination key

end Unitary

section Support

variable {F : Ent → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)

include hFc in
theorem hasCompactSupport_fderiv' : HasCompactSupport (fderiv ℝ F) := hFc.fderiv ℝ

include hF hFc in
theorem exists_bound₀ : ∃ M : ℝ, ∀ E, ‖F E‖ ≤ M := hF.continuous.bounded_above_of_compact_support hFc

include hF hFc in
theorem exists_bound₁ : ∃ M : ℝ, ∀ E, ‖fderiv ℝ F E‖ ≤ M :=
  (contDiff_fderiv' hF).continuous.bounded_above_of_compact_support (hasCompactSupport_fderiv' hFc)

theorem fderiv_eq_zero_of_notMem_tsupport {E : Ent} (h : E ∉ tsupport F) : fderiv ℝ F E = 0 :=
  Function.notMem_support.1 fun h' => h (support_fderiv_subset ℝ h')

theorem fderiv₂_eq_zero_of_notMem_tsupport {E : Ent} (h : E ∉ tsupport F) : fderiv ℝ (fderiv ℝ F) E = 0 :=
  Function.notMem_support.1 fun h' => h (tsupport_fderiv_subset ℝ (support_fderiv_subset ℝ h'))

include hFc in

theorem exists_radius : ∃ R : ℝ, 0 ≤ R ∧
    ∀ E : Ent, R < ‖E‖ → F E = 0 ∧ fderiv ℝ F E = 0 ∧ fderiv ℝ (fderiv ℝ F) E = 0 := by
  obtain ⟨R, hR⟩ := hFc.isCompact.isBounded.exists_norm_le
  refine ⟨max R 0, le_max_right _ _, fun E hE => ?_⟩
  have hnot : E ∉ tsupport F := fun h => by
    have := hR E h
    linarith [le_max_left R 0]
  exact ⟨image_eq_zero_of_notMem_tsupport hnot, fderiv_eq_zero_of_notMem_tsupport hnot,
    fderiv₂_eq_zero_of_notMem_tsupport hnot⟩

end Support

section Split

def Bm1 (c l : ℂ) (s : ℝ) : Ent :=
  mk (c * l * Complex.exp ((s : ℂ) * l)) 0 0 (-(c * l) * Complex.exp (-((s : ℂ) * l)))

def Bm2 (c l : ℂ) (s : ℝ) : Ent :=
  mk (c * l ^ 2 * Complex.exp ((s : ℂ) * l)) 0 0 (c * l ^ 2 * Complex.exp (-((s : ℂ) * l)))

theorem hasDerivAt_ofReal_mul (l : ℂ) (s : ℝ) : HasDerivAt (fun s : ℝ => (s : ℂ) * l) l s := by
  simpa using ((hasDerivAt_id (s : ℂ)).mul_const l).comp_ofReal

theorem hasDerivAt_exp_mul (l : ℂ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * l)) (Complex.exp ((s : ℂ) * l) * l) s :=
  (hasDerivAt_ofReal_mul l s).cexp

theorem hasDerivAt_exp_neg_mul (l : ℂ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (-((s : ℂ) * l))) (Complex.exp (-((s : ℂ) * l)) * (-l)) s :=
  (hasDerivAt_ofReal_mul l s).neg.cexp

theorem hasDerivAt_Bm (c l v : ℂ) (s : ℝ) : HasDerivAt (fun s : ℝ => Bm c ((s : ℂ) * l) v) (Bm1 c l s) s := by
  unfold Bm Bm1
  refine hasDerivAt_mk ?_ (hasDerivAt_const _ _) (hasDerivAt_const _ _) ?_
  · have := (hasDerivAt_exp_mul l s).const_mul c
    convert this using 1 <;> first | rfl | ring1 | (funext _; ring1)
  · have := (hasDerivAt_exp_neg_mul l s).const_mul c
    convert this using 1 <;> first | rfl | ring1 | (funext _; ring1)

theorem hasDerivAt_Bm1 (c l : ℂ) (s : ℝ) : HasDerivAt (Bm1 c l) (Bm2 c l s) s := by
  unfold Bm1 Bm2
  refine hasDerivAt_mk ?_ (hasDerivAt_const _ _) (hasDerivAt_const _ _) ?_
  · have := (hasDerivAt_exp_mul l s).const_mul (c * l)
    convert this using 1 <;> first | rfl | ring1 | (funext _; ring1)
  · have := (hasDerivAt_exp_neg_mul l s).const_mul (-(c * l))
    convert this using 1 <;> first | rfl | ring1 | (funext _; ring1)

theorem continuous_Bm_v (c w : ℂ) : Continuous fun v : ℂ => Bm c w v := by
  unfold Bm
  exact continuous_mk continuous_const continuous_id continuous_const continuous_const

theorem continuous_Bm_s (c l v : ℂ) : Continuous fun s : ℝ => Bm c ((s : ℂ) * l) v := by
  unfold Bm
  refine continuous_mk ?_ continuous_const continuous_const ?_ <;> fun_prop

theorem continuous_Bm1 (c l : ℂ) : Continuous (Bm1 c l) := by
  unfold Bm1
  refine continuous_mk ?_ continuous_const continuous_const ?_ <;> fun_prop

theorem continuous_Bm2 (c l : ℂ) : Continuous (Bm2 c l) := by
  unfold Bm2
  refine continuous_mk ?_ continuous_const continuous_const ?_ <;> fun_prop

theorem Bm1_zero (c l : ℂ) : Bm1 c l 0 = (c * l) • Dg := by
  rw [Bm1, Dg, smul_mk, mk_eq_mk_iff]
  simp

theorem Bm2_zero (c l : ℂ) : Bm2 c l 0 = (c * l ^ 2) • One := by
  rw [Bm2, One, smul_mk, mk_eq_mk_iff]
  simp

theorem Bm_ofReal_zero_mul (c l v : ℂ) : Bm c (((0 : ℝ) : ℂ) * l) v = pt c v := by
  rw [Complex.ofReal_zero, zero_mul, Bm_zero]

variable {F : Ent → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) (c : ℂ)
  {ε : ℝ} (hε : 0 < ε) (hvan : ∀ w : ℂ, w ≠ 0 → ‖w‖ < ε → ∫ v : ℂ, F (Bm c w v) = 0)

include hF hFc hε hvan

theorem integral_second_deriv_split {l : ℂ} (hl : ‖l‖ = 1) :
    Integrable (fun v : ℂ => fderiv ℝ (fderiv ℝ F) (pt c v) ((c * l) • Dg) ((c * l) • Dg) +
        fderiv ℝ F (pt c v) ((c * l ^ 2) • One)) ∧
      ∫ v : ℂ, (fderiv ℝ (fderiv ℝ F) (pt c v) ((c * l) • Dg) ((c * l) • Dg) +
        fderiv ℝ F (pt c v) ((c * l ^ 2) • One)) = 0 := by
  obtain ⟨R, hR0, hzero⟩ := exists_radius hFc
  obtain ⟨M₀, hM₀⟩ := exists_bound₀ hF hFc
  have hl0 : l ≠ 0 := norm_ne_zero_iff.1 (by rw [hl]; exact one_ne_zero)

  set φ : Ent × ℝ → ℂ := fun q => fderiv ℝ (fderiv ℝ F) q.1 (Bm1 c l q.2) (Bm1 c l q.2) +
    fderiv ℝ F q.1 (Bm2 c l q.2) with hφ
  have hφc : Continuous φ := by
    have h1 : Continuous fun q : Ent × ℝ => fderiv ℝ (fderiv ℝ F) q.1 :=
      (contDiff_fderiv₂ hF).continuous.comp continuous_fst
    have h2 : Continuous fun q : Ent × ℝ => fderiv ℝ F q.1 := (contDiff_fderiv' hF).continuous.comp continuous_fst
    have h3 : Continuous fun q : Ent × ℝ => Bm1 c l q.2 := (continuous_Bm1 c l).comp continuous_snd
    have h4 : Continuous fun q : Ent × ℝ => Bm2 c l q.2 := (continuous_Bm2 c l).comp continuous_snd
    exact ((h1.clm_apply h3).clm_apply h3).add (h2.clm_apply h4)
  obtain ⟨M', hM'⟩ := (hFc.isCompact.prod (isCompact_Icc (a := (-1 : ℝ)) (b := 1))).exists_bound_of_continuousOn
    hφc.continuousOn
  set M : ℝ := max M' 0 with hM
  have hφb : ∀ (E : Ent) (s : ℝ), |s| ≤ 1 → ‖φ (E, s)‖ ≤ M := by
    intro E s hs
    by_cases hE : E ∈ tsupport F
    · exact (hM' (E, s) ⟨hE, abs_le.1 hs⟩).trans (le_max_left _ _)
    · simp only [hφ, fderiv_eq_zero_of_notMem_tsupport hE, fderiv₂_eq_zero_of_notMem_tsupport hE,
        ContinuousLinearMap.zero_apply, add_zero, norm_zero]
      exact le_max_right _ _

  set G : ℝ → ℂ → ℂ := fun s v => F (Bm c ((s : ℂ) * l) v) with hG
  set G₁ : ℝ → ℂ → ℂ := fun s v => fderiv ℝ F (Bm c ((s : ℂ) * l) v) (Bm1 c l s) with hG₁
  set G₂ : ℝ → ℂ → ℂ := fun s v => fderiv ℝ (fderiv ℝ F) (Bm c ((s : ℂ) * l) v) (Bm1 c l s) (Bm1 c l s) +
    fderiv ℝ F (Bm c ((s : ℂ) * l) v) (Bm2 c l s) with hG₂
  have hGd : ∀ s v, HasDerivAt (fun s => G s v) (G₁ s v) s := fun s v =>
    hasDerivAt_comp_curve hF (fun s => hasDerivAt_Bm c l v s) s
  have hG₁d : ∀ s v, HasDerivAt (fun s => G₁ s v) (G₂ s v) s := fun s v =>
    hasDerivAt_fderiv_comp_curve hF (fun s => hasDerivAt_Bm c l v s) (hasDerivAt_Bm1 c l s)
  have hG₂c : ∀ v, Continuous fun s => G₂ s v := by
    intro v
    have h1 : Continuous fun s : ℝ => fderiv ℝ (fderiv ℝ F) (Bm c ((s : ℂ) * l) v) :=
      (contDiff_fderiv₂ hF).continuous.comp (continuous_Bm_s c l v)
    have h2 : Continuous fun s : ℝ => fderiv ℝ F (Bm c ((s : ℂ) * l) v) :=
      (contDiff_fderiv' hF).continuous.comp (continuous_Bm_s c l v)
    exact ((h1.clm_apply (continuous_Bm1 c l)).clm_apply (continuous_Bm1 c l)).add
      (h2.clm_apply (continuous_Bm2 c l))

  have hfar : ∀ s v, R < ‖v‖ →
      F (Bm c ((s : ℂ) * l) v) = 0 ∧ fderiv ℝ F (Bm c ((s : ℂ) * l) v) = 0 ∧
        fderiv ℝ (fderiv ℝ F) (Bm c ((s : ℂ) * l) v) = 0 := fun s v hv =>
    hzero _ (lt_of_lt_of_le hv (norm_v_le_Bm c _ v))

  have hint : ∀ s, Integrable (G s) (volume : Measure ℂ) := by
    intro s
    refine Continuous.integrable_of_hasCompactSupport (hF.continuous.comp (continuous_Bm_v c _)) ?_
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) R) fun v hv => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hv
    exact (hfar s v hv).1
  have hmeas : AEStronglyMeasurable (G₂ 0) (volume : Measure ℂ) := by
    have h1 : Continuous fun v : ℂ => fderiv ℝ (fderiv ℝ F) (Bm c (((0 : ℝ) : ℂ) * l) v) :=
      (contDiff_fderiv₂ hF).continuous.comp (continuous_Bm_v c _)
    have h2 : Continuous fun v : ℂ => fderiv ℝ F (Bm c (((0 : ℝ) : ℂ) * l) v) :=
      (contDiff_fderiv' hF).continuous.comp (continuous_Bm_v c _)
    exact (((h1.clm_apply continuous_const).clm_apply continuous_const).add
      (h2.clm_apply continuous_const)).aestronglyMeasurable

  set bound₀ : ℂ → ℝ := (Metric.closedBall (0 : ℂ) R).indicator fun _ => M₀ with hb₀
  set bound₂ : ℂ → ℝ := (Metric.closedBall (0 : ℂ) R).indicator fun _ => M with hb₂
  have hb₀i : Integrable bound₀ (volume : Measure ℂ) :=
    (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
      (integrableOn_const (hs := measure_closedBall_lt_top.ne))
  have hb₂i : Integrable bound₂ (volume : Measure ℂ) :=
    (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
      (integrableOn_const (hs := measure_closedBall_lt_top.ne))
  have hGb : ∀ s v, |s| ≤ 1 → ‖G s v‖ ≤ bound₀ v := by
    intro s v hs
    by_cases hv : ‖v‖ ≤ R
    · have hmem : v ∈ Metric.closedBall (0 : ℂ) R := by rwa [Metric.mem_closedBall, dist_zero_right]
      simp only [hb₀, Set.indicator_of_mem hmem, hG]
      exact hM₀ _
    · have hmem : v ∉ Metric.closedBall (0 : ℂ) R := by rwa [Metric.mem_closedBall, dist_zero_right]
      simp only [hb₀, Set.indicator_of_notMem hmem, hG, (hfar s v (not_le.1 hv)).1, norm_zero, le_refl]
  have hG₂b : ∀ s v, |s| ≤ 1 → ‖G₂ s v‖ ≤ bound₂ v := by
    intro s v hs
    by_cases hv : ‖v‖ ≤ R
    · have hmem : v ∈ Metric.closedBall (0 : ℂ) R := by rwa [Metric.mem_closedBall, dist_zero_right]
      simp only [hb₂, Set.indicator_of_mem hmem, hG₂]
      exact hφb _ s hs
    · have hmem : v ∉ Metric.closedBall (0 : ℂ) R := by rwa [Metric.mem_closedBall, dist_zero_right]
      have hf := hfar s v (not_le.1 hv)
      simp only [hb₂, Set.indicator_of_notMem hmem, hG₂, hf.2.1, hf.2.2, ContinuousLinearMap.zero_apply,
        add_zero, norm_zero, le_refl]
  have hvan' : ∀ s : ℝ, s ≠ 0 → |s| < ε → ∫ v, G s v = 0 := by
    intro s hs hsε
    refine hvan ((s : ℂ) * l) (mul_ne_zero (Complex.ofReal_ne_zero.2 hs) hl0) ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hl, mul_one]
    exact hsε
  have key := integral_secondDeriv_eq_zero G G₁ G₂ hGd hG₁d hG₂c hint hmeas bound₀ bound₂ hb₀i hb₂i hGb hG₂b
    hε hvan'

  have hG₂0 : G₂ 0 = fun v : ℂ => fderiv ℝ (fderiv ℝ F) (pt c v) ((c * l) • Dg) ((c * l) • Dg) +
      fderiv ℝ F (pt c v) ((c * l ^ 2) • One) := by
    funext v
    simp only [hG₂, Bm_ofReal_zero_mul, Bm1_zero, Bm2_zero]
  refine ⟨?_, by rw [← hG₂0]; exact key⟩
  rw [← hG₂0]
  refine hb₂i.mono' hmeas (Filter.Eventually.of_forall fun v => hG₂b 0 v (by simp))

end Split

section Polar

variable {F : Ent → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) (c : ℂ)

include hF hFc

def dir (θ : ℝ) : ℂ := (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I

omit hF hFc in
theorem norm_dir (θ : ℝ) : ‖dir θ‖ = 1 := by
  have h : ‖dir θ‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, dir, Complex.normSq_add_mul_I, Real.cos_sq_add_sin_sq]
  have h0 : 0 ≤ ‖dir θ‖ := norm_nonneg _
  nlinarith [h, h0]

omit hF hFc in
theorem hasDerivAt_pt_ray (θ : ℝ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => pt c ((r : ℂ) * dir θ)) (dir θ • E12) r := by
  have h : HasDerivAt (fun r : ℝ => pt c ((r : ℂ) * dir θ)) (mk 0 (dir θ) 0 0) r := by
    unfold pt
    exact hasDerivAt_mk (hasDerivAt_const _ _) (hasDerivAt_ofReal_mul (dir θ) r) (hasDerivAt_const _ _)
      (hasDerivAt_const _ _)
  convert h using 1
  rw [E12, smul_mk, mk_eq_mk_iff]
  simp

theorem integral_inv_norm_sq_smul_fderiv :
    ∫ v : ℂ, (‖v‖ ^ 2)⁻¹ • fderiv ℝ F (pt c v) (v • E12) = -((2 * Real.pi) • F (pt c 0)) := by
  obtain ⟨R, hR0, hzero⟩ := exists_radius hFc
  obtain ⟨M₁, hM₁⟩ := exists_bound₁ hF hFc
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)

  rw [← Complex.integral_comp_polarCoord_symm]
  set g : ℝ × ℝ → ℂ := fun p => fderiv ℝ F (pt c ((p.1 : ℂ) * dir p.2)) (dir p.2 • E12) with hg
  have hcongr : ∫ p in polarCoord.target, p.1 • ((‖Complex.polarCoord.symm p‖ ^ 2)⁻¹ •
      fderiv ℝ F (pt c (Complex.polarCoord.symm p)) (Complex.polarCoord.symm p • E12)) =
        ∫ p in polarCoord.target, g p := by
    refine setIntegral_congr_fun polarCoord.open_target.measurableSet fun p hp => ?_
    have hp1 : 0 < p.1 := by
      rw [polarCoord_target] at hp
      exact hp.1
    have hx : Complex.polarCoord.symm p = (p.1 : ℂ) * dir p.2 := by
      rw [Complex.polarCoord_symm_apply, dir]
    have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    simp only [hg]
    rw [hnorm, hx, mul_smul, Complex.coe_smul, map_smul]
    rw [smul_smul, smul_smul]
    have : p.1 * (p.1 ^ 2)⁻¹ * p.1 = 1 := by field_simp
    rw [this, one_smul]
  rw [hcongr, polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict]

  have hgzero : ∀ p : ℝ × ℝ, R < |p.1| → g p = 0 := by
    intro p hp
    have hn : R < ‖pt c ((p.1 : ℂ) * dir p.2)‖ := by
      refine lt_of_lt_of_le ?_ (norm_v_le_pt c _)
      rwa [norm_mul, Complex.norm_real, norm_dir, mul_one, Real.norm_eq_abs]
    simp only [hg, (hzero _ hn).2.1, ContinuousLinearMap.zero_apply]
  have hgb : ∀ p : ℝ × ℝ, ‖g p‖ ≤ (Set.Icc (-R) R).indicator (fun _ => M₁) p.1 * (fun _ : ℝ => (1 : ℝ)) p.2 := by
    intro p
    by_cases hp : |p.1| ≤ R
    · have hmem : p.1 ∈ Set.Icc (-R) R := abs_le.1 hp
      rw [Set.indicator_of_mem hmem, mul_one]
      calc ‖g p‖ ≤ ‖fderiv ℝ F (pt c ((p.1 : ℂ) * dir p.2))‖ * ‖dir p.2 • E12‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ M₁ * 1 := by
            gcongr
            · exact hM₁ _
            · rw [norm_smul, norm_dir, one_mul, E12]
              exact norm_mk_le zero_le_one (by simp) (by simp) (by simp) (by simp)
        _ = M₁ := mul_one _
    · rw [hgzero p (not_le.1 hp), norm_zero]
      exact mul_nonneg (Set.indicator_nonneg (fun _ _ => hM₁0) _) zero_le_one
  have hgc : Continuous g := by
    have h1 : Continuous fun p : ℝ × ℝ => pt c ((p.1 : ℂ) * dir p.2) := by
      unfold pt dir
      refine continuous_mk continuous_const ?_ continuous_const continuous_const
      fun_prop
    have h2 : Continuous fun p : ℝ × ℝ => dir p.2 • E12 := by
      unfold dir
      fun_prop
    exact ((contDiff_fderiv' hF).continuous.comp h1).clm_apply h2
  have hgi : Integrable g (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
      ((volume : Measure ℝ).restrict (Set.Ioo (-Real.pi) Real.pi))) := by
    have h1 : Integrable ((Set.Icc (-R) R).indicator fun _ => M₁) ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
      refine (integrable_indicator_iff measurableSet_Icc).2 ?_
      refine integrableOn_const (hs := ?_)
      rw [Measure.restrict_apply measurableSet_Icc]
      exact ((measure_mono Set.inter_subset_left).trans_lt measure_Icc_lt_top).ne
    have h2 : Integrable (fun _ : ℝ => (1 : ℝ)) ((volume : Measure ℝ).restrict (Set.Ioo (-Real.pi) Real.pi)) :=
      integrable_const _
    exact (h1.mul_prod h2).mono' hgc.aestronglyMeasurable (Filter.Eventually.of_forall hgb)
  rw [integral_prod_symm g hgi]

  have hinner : ∀ θ : ℝ, ∫ r in Set.Ioi (0 : ℝ), g (r, θ) = -F (pt c 0) := by
    intro θ
    have hderiv : ∀ r ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun r : ℝ => F (pt c ((r : ℂ) * dir θ))) (g (r, θ)) r :=
      fun r _ => hasDerivAt_comp_curve hF (hasDerivAt_pt_ray c θ) r
    have hcont : Continuous fun r : ℝ => F (pt c ((r : ℂ) * dir θ)) := by
      refine hF.continuous.comp ?_
      unfold pt
      exact continuous_mk continuous_const (by fun_prop) continuous_const continuous_const
    have hzero' : ∀ r : ℝ, R < r → F (pt c ((r : ℂ) * dir θ)) = 0 := by
      intro r hr
      have hn : R < ‖pt c ((r : ℂ) * dir θ)‖ := by
        refine lt_of_lt_of_le ?_ (norm_v_le_pt c _)
        rw [norm_mul, Complex.norm_real, norm_dir, mul_one, Real.norm_eq_abs]
        exact lt_of_lt_of_le hr (le_abs_self r)
      exact (hzero _ hn).1
    have hgθc : Continuous fun r : ℝ => g (r, θ) := hgc.comp (continuous_id.prodMk continuous_const)
    have hint : IntegrableOn (fun r : ℝ => g (r, θ)) (Set.Ioi 0) := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi hR0]
      refine IntegrableOn.union ?_ ?_
      · exact (hgθc.continuousOn.integrableOn_Icc (a := 0) (b := R)).mono_set Set.Ioc_subset_Icc_self
      · refine integrableOn_zero.congr_fun (fun r hr => ?_) measurableSet_Ioi
        exact (hgzero (r, θ) (lt_of_lt_of_le hr (le_abs_self r))).symm
    have hlim : Tendsto (fun r : ℝ => F (pt c ((r : ℂ) * dir θ))) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      exact (Filter.eventually_gt_atTop R).mono fun r hr => (hzero' r hr).symm
    rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont.continuousWithinAt hderiv hint hlim]
    simp
  simp_rw [hinner]
  rw [integral_const, smul_neg]
  congr 1
  rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  congr 1
  ring

end Polar

theorem main (F : Ent → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (hinv : ∀ u : Matrix (Fin 2) (Fin 2) ℂ, u ∈ Matrix.unitaryGroup (Fin 2) ℂ →
      ∀ E : Ent, F (Matrix.of.symm (u * Matrix.of E * star u)) = F E)
    (c : ℂ) (hc : c ≠ 0)
    (hvan : ∃ ε : ℝ, 0 < ε ∧ ∀ w : ℂ, w ≠ 0 → ‖w‖ < ε →
      ∫ v : ℂ, F (Matrix.of.symm !![c * Complex.exp w, v; 0, c * Complex.exp (-w)]) = 0) :
    F (Matrix.of.symm !![c, 0; 0, c]) = 0 := by
  obtain ⟨ε, hε, hvan⟩ := hvan
  change ∀ w : ℂ, w ≠ 0 → ‖w‖ < ε → ∫ v : ℂ, F (Bm c w v) = 0 at hvan
  change F (pt c 0) = 0

  obtain ⟨hi₁, h₁⟩ := integral_second_deriv_split hF hFc c hε hvan (l := 1) (by simp)
  obtain ⟨hi₂, h₂⟩ := integral_second_deriv_split hF hFc c hε hvan (l := Complex.I) (by simp)
  set T : ℂ → ℂ := fun v => fderiv ℝ (fderiv ℝ F) (pt c v) Dg Dg +
    fderiv ℝ (fderiv ℝ F) (pt c v) (Complex.I • Dg) (Complex.I • Dg) with hT

  have hsum : ∀ v, (fderiv ℝ (fderiv ℝ F) (pt c v) ((c * 1) • Dg) ((c * 1) • Dg) +
        fderiv ℝ F (pt c v) ((c * 1 ^ 2) • One)) +
      (fderiv ℝ (fderiv ℝ F) (pt c v) ((c * Complex.I) • Dg) ((c * Complex.I) • Dg) +
        fderiv ℝ F (pt c v) ((c * Complex.I ^ 2) • One)) = (‖c‖ ^ 2 : ℝ) • T v := by
    intro v
    have hcD : (c * 1) • Dg = c.re • Dg + c.im • (Complex.I • Dg) := by
      rw [mul_one, ← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul, Complex.re_add_im]
    have hcID : (c * Complex.I) • Dg = (-c.im) • Dg + c.re • (Complex.I • Dg) := by
      rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul]
      congr 1
      apply Complex.ext <;> simp
    have hOne : (c * Complex.I ^ 2) • One = -((c * 1 ^ 2) • One) := by
      rw [Complex.I_sq, one_pow, mul_one, mul_neg_one, neg_smul]
    rw [hOne, map_neg, hcD, hcID]
    simp only [hT, map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_pow]
    have hn : ((‖c‖ : ℂ)) ^ 2 = (c.re : ℂ) ^ 2 + (c.im : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      push_cast
      ring
    rw [hn]
    ring
  have hT0 : ∫ v, T v = 0 := by
    have e := integral_add hi₁ hi₂
    rw [h₁, h₂, add_zero] at e
    simp_rw [hsum] at e
    rw [integral_smul, smul_eq_zero] at e
    rcases e with e | e
    · exact absurd e (by positivity)
    · exact e

  have hae : (fun v => T v) =ᵐ[volume] fun v : ℂ => (4 : ℝ) • ((‖v‖ ^ 2)⁻¹ • fderiv ℝ F (pt c v) (v • E12)) := by
    have h0 : ({0} : Set ℂ)ᶜ ∈ ae (volume : Measure ℂ) := by
      rw [compl_mem_ae_iff, measure_singleton]
    refine Filter.eventuallyEq_of_mem h0 fun v hv => ?_
    have hv : v ≠ 0 := hv
    have hp := pointwise_identity hF hinv c hv
    have hv2 : (‖v‖ ^ 2 : ℝ) ≠ 0 := by positivity
    rw [smul_comm, ← hp, hT, inv_smul_smul₀ hv2]
  have hJ : ∫ v : ℂ, (‖v‖ ^ 2)⁻¹ • fderiv ℝ F (pt c v) (v • E12) = 0 := by
    have e := integral_congr_ae hae
    rw [hT0, integral_smul, eq_comm, smul_eq_zero] at e
    rcases e with e | e
    · norm_num at e
    · exact e

  rw [integral_inv_norm_sq_smul_fderiv hF hFc c, neg_eq_zero, smul_eq_zero] at hJ
  rcases hJ with e | e
  · exact absurd e (by positivity)
  · exact e

end P2mHCLimitC
p2m_reactivate "P2MW.S_AutomorphicForm_apply_scalar_eq_zero_of_conj_unitary_eq_of_forall_integral_upperTriangular_complex_eq_zero.P2mHCLimitC"

end
p2m_reactivate "P2MW.S_AutomorphicForm_apply_scalar_eq_zero_of_conj_unitary_eq_of_forall_integral_upperTriangular_complex_eq_zero.P2mHCLimitC"

theorem solution
    (F : (Fin 2 → Fin 2 → ℂ) → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (hinv : ∀ u : Matrix (Fin 2) (Fin 2) ℂ, u ∈ Matrix.unitaryGroup (Fin 2) ℂ →
      ∀ E : Fin 2 → Fin 2 → ℂ, F (Matrix.of.symm (u * Matrix.of E * star u)) = F E)
    (c : ℂ) (hc : c ≠ 0)
    (hvan : ∃ ε : ℝ, 0 < ε ∧ ∀ w : ℂ, w ≠ 0 → ‖w‖ < ε →
      ∫ v : ℂ, F (Matrix.of.symm !![c * Complex.exp w, v; 0, c * Complex.exp (-w)]) = 0) :
    F (Matrix.of.symm !![c, 0; 0, c]) = 0 :=
  P2mHCLimitC.main F hF hFc hinv c hc hvan

end S_AutomorphicForm_apply_scalar_eq_zero_of_conj_unitary_eq_of_forall_integral_upperTriangular_complex_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_apply_scalar_eq_zero_of_conj_unitary_eq_of_forall_integral_upperTriangular_complex_eq_zero (solution)
