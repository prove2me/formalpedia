-- Prove2me | solution 1 for AtaBarjesteh23.Workload.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T20:47:54.442512+00:00
-- url     : https://prove2.me/submissions/739f3153-22c4-4b05-9e36-c21318cdf164
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting
import Definitions.Def_AtaBarjesteh23_Workload_DriftBM
import Definitions.Def_AtaBarjesteh23_Workload_Control
import Theorems.Thm_AtaBarjesteh23_Workload_proposition_2
import Theorems.Thm_AtaBarjesteh23_Workload_proposition_3
import Theorems.Thm_AtaBarjesteh23_Workload_corollary_2
import Theorems.Thm_AtaBarjesteh23_Workload_lemma_2
import Theorems.Thm_AtaBarjesteh23_Workload_theorem_1_optimality

open MeasureTheory Set Filter Topology

theorem AtaB_basic (M : AtaBarjesteh23.Workload.Model) (hM : M.Standing) :
    0 < M.hStar ∧ 0 < M.bStar ∧ 0 < M.kappa ∧ 0 < M.a ∧ 0 ≤ M.μ ∧ 0 < M.σ ∧
    (∀ w, 0 ≤ w → M.hcost w = M.hStar * w) ∧ (∀ w ≤ 0, M.hcost w = -(M.bStar * w)) ∧
    Continuous M.hcost := by
  obtain ⟨hK, hm, hh, hb, hr, hH, hμ, hσ⟩ := hM
  have : Nonempty (Fin M.K) := ⟨⟨0, hK⟩⟩
  have hbs : 0 < M.bStar := by
    obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := fun k : Fin M.K => M.b k / M.m k)
    rw [AtaBarjesteh23.Workload.Model.bStar, ← hk]
    exact div_pos (hb k) (hm k)
  have hhs : 0 < M.hStar := by
    obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := fun k : Fin M.K => M.h k / M.m k)
    rw [AtaBarjesteh23.Workload.Model.hStar, ← hk]
    exact div_pos (hh k) (hm k)
  have hks : 0 < M.kappa := by
    obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := fun k : Fin M.K => M.r k / M.m k)
    rw [AtaBarjesteh23.Workload.Model.kappa, ← hk]
    exact div_pos (hr k) (hm k)
  have hmne : M.m ≠ 0 := by
    intro h
    have := hm ⟨0, hK⟩
    rw [h] at this
    simp at this
  have ha : 0 < M.a := by
    have := hH.inv.dotProduct_mulVec_pos hmne
    simpa [AtaBarjesteh23.Workload.Model.a] using this
  have hhmax : ∀ w, M.hcost w = max (M.hStar * w) (-(M.bStar * w)) := by
    intro w
    unfold AtaBarjesteh23.Workload.Model.hcost
    split_ifs with h
    · rw [max_eq_left]; nlinarith
    · rw [max_eq_right]; push_neg at h; nlinarith
  refine ⟨hhs, hbs, hks, ha, hμ, hσ, ?_, ?_, ?_⟩
  · intro w hw; rw [hhmax, max_eq_left]; nlinarith
  · intro w hw; rw [hhmax, max_eq_right]; nlinarith
  · have : M.hcost = fun w => max (M.hStar * w) (-(M.bStar * w)) := funext hhmax
    rw [this]; fun_prop

theorem AtaB_lip_quad (c1 c2 d R : ℝ) (hR : 0 ≤ R) :
    LipschitzOnWith (Real.toNNReal (2 * |c1| * R + |c2|)) (fun y => c1 * y ^ 2 + c2 * y + d)
      (Metric.closedBall 0 R) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hx hy
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  have : c1 * x ^ 2 + c2 * x + d - (c1 * y ^ 2 + c2 * y + d) = (c1 * (x + y) + c2) * (x - y) := by
    ring
  rw [this, abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  calc |c1 * (x + y) + c2| ≤ |c1 * (x + y)| + |c2| := abs_add_le _ _
    _ = |c1| * |x + y| + |c2| := by rw [abs_mul]
    _ ≤ |c1| * (|x| + |y|) + |c2| := by gcongr; exact abs_add_le _ _
    _ ≤ 2 * |c1| * R + |c2| := by nlinarith [abs_nonneg c1]

theorem AtaB_le_of_eps (a b c : ℝ) (hc : 0 < c) (h : ∀ ε > 0, a ≤ b + ε * c) : a ≤ b := by
  by_contra hab
  push_neg at hab
  have := h ((a - b) / (2 * c)) (div_pos (sub_pos.mpr hab) (by positivity))
  have e : (a - b) / (2 * c) * c = (a - b) / 2 := by field_simp
  rw [e] at this
  linarith

/-- Reflection `s ↦ u - s` maps derivatives within `[0, u]` to derivatives within `[0, u]`. -/
theorem AtaB_reflect {u : ℝ} {f : ℝ → ℝ} {f' : ℝ → ℝ}
    (hf : ∀ w ∈ Icc 0 u, HasDerivWithinAt f (f' w) (Icc 0 u) w) :
    ∀ s ∈ Icc 0 u, HasDerivWithinAt (fun s => f (u - s)) (-f' (u - s)) (Icc 0 u) s := by
  intro s hs
  have hmaps : MapsTo (fun s => u - s) (Icc 0 u) (Icc 0 u) := by
    intro x hx; simp only [mem_Icc] at hx ⊢; constructor <;> linarith [hx.1, hx.2]
  have h := (hf (u - s) (hmaps hs)).comp s ((hasDerivAt_id s).const_sub u).hasDerivWithinAt hmaps
  exact h.congr_deriv (by ring)

open AtaBarjesteh23.Workload

theorem AtaB_f_deriv (M : Model) (hM : M.Standing) :
    ∀ w ∈ Icc M.lStar M.uStar, HasDerivWithinAt M.fStar (M.vStar w) (Icc M.lStar M.uStar) w := by
  obtain ⟨-, -, hC1, hBV, -⟩ := proposition_3 M hM
  have hlu := hBV.1
  set l := M.lStar
  set u := M.uStar
  set e : ℝ → ℝ := fun x => max l (min x u) with he
  have hemem : ∀ x, e x ∈ Icc l u := fun x => ⟨le_max_left _ _, max_le hlu.le (min_le_right _ _)⟩
  have heid : ∀ x ∈ Icc l u, e x = x := fun x hx => by
    simp only [e]; rw [min_eq_left hx.2, max_eq_right hx.1]
  have hvc : Continuous (M.vStar ∘ e) :=
    hC1.continuousOn.comp_continuous (by fun_prop) hemem
  have hfeq : ∀ x ∈ Icc l u, M.fStar x = ∫ t in l..x, (M.vStar ∘ e) t := by
    intro x hx
    simp only [Model.fStar]
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [uIcc_of_le hx.1] at ht
    simp only [Function.comp, heid t ⟨ht.1, ht.2.trans hx.2⟩]
  intro w hw
  have h := (hvc.integral_hasStrictDerivAt l w).hasDerivAt.hasDerivWithinAt (s := Icc l u)
  have h2 := h.congr (fun x hx => hfeq x hx) (hfeq w hw)
  simpa [Function.comp, heid w hw] using h2

theorem AtaB_iter2 {f : ℝ → ℝ} {s : Set ℝ} :
    iteratedDerivWithin 2 f s = derivWithin (derivWithin f s) s := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDerivWithin_succ', iteratedDerivWithin_one]

theorem AtaB_bellman_value (M : Model) (hM : M.Standing) (γ y G2 hw : ℝ)
    (h : IsLeast (range fun x : ℝ =>
        M.σ ^ 2 / 2 * G2 + M.μ * y - x * y + M.cost x + hw) γ) :
    G2 = M.a / (2 * M.σ ^ 2) * y ^ 2 - 2 * M.μ / M.σ ^ 2 * y + 2 * (γ - hw) / M.σ ^ 2 := by
  obtain ⟨-, -, -, -, -, hσ, -⟩ := AtaB_basic M hM
  obtain ⟨⟨⟨x0, hx0⟩, hmax⟩, -⟩ := lemma_2 M hM y
  set m := M.σ ^ 2 / 2 * G2 + M.μ * y + hw - M.a / 4 * y ^ 2
  have hE : ∀ x, M.σ ^ 2 / 2 * G2 + M.μ * y - x * y + M.cost x + hw
      = m + (M.a / 4 * y ^ 2 - (y * x - M.cost x)) := by intro x; simp only [m]; ring
  have hm : IsLeast (range fun x : ℝ =>
      M.σ ^ 2 / 2 * G2 + M.μ * y - x * y + M.cost x + hw) m := by
    refine ⟨⟨x0, ?_⟩, ?_⟩
    · simp only at hx0 ⊢; rw [hE, hx0]; ring
    · rintro _ ⟨x, rfl⟩
      simp only
      rw [hE]
      have := hmax ⟨x, rfl⟩
      simp only at this
      linarith
  have := h.unique hm
  have hσ2 : 0 < M.σ ^ 2 := by positivity
  simp only [m] at this
  field_simp
  linarith

set_option maxHeartbeats 1000000 in
theorem solution (M : Model) (hM : M.Standing)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ mΩ) (B : ℝ → Ω → ℝ) (hB : IsDriftBM 𝔽 P B M.μ M.σ) :
    (∀ L U W : ℝ → Ω → ℝ,
      IsBarrierPolicy 𝔽 P B M.lStar M.uStar (fun t ω => M.thetaStar (W t ω)) L U W →
      Tendsto (fun t => M.avgCost P (fun t ω => M.thetaStar (W t ω)) L W t) atTop
        (𝓝 (ENNReal.ofReal M.gammaStar))) ∧
    (∀ θ L U W : ℝ → Ω → ℝ, IsAdmissible 𝔽 P B θ L U W →
      ENNReal.ofReal M.gammaStar ≤ limsup (fun t => M.avgCost P θ L W t) atTop) := by
  refine ⟨?_, theorem_1_optimality M hM P 𝔽 B hB⟩
  intro L U W hpol
  obtain ⟨-, -, hC1, hBV, -⟩ := proposition_3 M hM
  obtain ⟨-, -, hC2, hBF, -⟩ := corollary_2 M hM
  have hlu := hBV.1
  set l := M.lStar
  set u := M.uStar
  set s := Icc l u with hs
  have hUD : UniqueDiffOn ℝ s := uniqueDiffOn_Icc hlu
  have hdf : ∀ w ∈ s, derivWithin M.fStar s w = M.vStar w := fun w hw =>
    (AtaB_f_deriv M hM w hw).derivWithin (hUD w hw)
  -- a measurable (continuous) version of the drift that agrees with `θ⋆` on `[l⋆, u⋆]`
  set e : ℝ → ℝ := fun x => max l (min x u) with he
  have hemem : ∀ x, e x ∈ Icc l u := fun x => ⟨le_max_left _ _, max_le hlu.le (min_le_right _ _)⟩
  have heid : ∀ x ∈ Icc l u, e x = x := fun x hx => by
    simp only [e]; rw [min_eq_left hx.2, max_eq_right hx.1]
  set θf : ℝ → ℝ := fun w => M.a / 2 * M.vStar (e w) with hθf
  have hθc : Continuous θf :=
    continuous_const.mul (hC1.continuousOn.comp_continuous (by fun_prop) hemem)
  have hθeq : ∀ w ∈ s, θf w = M.thetaStar w := fun w hw => by
    simp only [θf, Model.thetaStar, heid w hw]
  obtain ⟨hlu', hadm, hWmem, hstil⟩ := hpol
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hadm
  have hWeq : ∀ t ω, 0 ≤ t → θf (W t ω) = M.thetaStar (W t ω) := fun t ω ht =>
    hθeq _ (hWmem t ω ht)
  have hpol' : IsBarrierPolicy 𝔽 P B l u (fun t ω => θf (W t ω)) L U W := by
    refine ⟨hlu', ⟨?_, ?_, h3, h4, ?_, h6⟩, hWmem, hstil⟩
    · have : (fun t ω => if 0 ≤ t then θf (W t ω) else 0) =
          (fun t ω => if 0 ≤ t then M.thetaStar (W t ω) else 0) := by
        funext t ω
        split_ifs with ht
        · exact hWeq t ω ht
        · rfl
      rw [this]; exact h1
    · intro ω t ht
      refine (intervalIntegrable_congr ?_).mpr (h2 ω t ht)
      intro x hx
      rw [uIoc_of_le ht] at hx
      exact hWeq x ω hx.1.le
    · intro t ω ht
      have hint : (∫ x in (0 : ℝ)..t, θf (W x ω)) = ∫ x in (0 : ℝ)..t, M.thetaStar (W x ω) := by
        refine intervalIntegral.integral_congr ?_
        intro x hx
        rw [uIcc_of_le ht] at hx
        exact hWeq x ω hx.1
      show W t ω = B t ω - (∫ x in (0 : ℝ)..t, θf (W x ω)) - U t ω + L t ω
      rw [hint]
      exact h5 t ω ht
  have h35 : ∀ w ∈ Ioo l u,
      M.σ ^ 2 / 2 * iteratedDerivWithin 2 M.fStar s w + M.μ * derivWithin M.fStar s w
        - θf w * derivWithin M.fStar s w + M.cost (θf w) + M.hcost w = M.gammaStar := by
    intro w hw
    have hwI : w ∈ s := Ioo_subset_Icc_self hw
    have hmin := hBF.2.2.1 w hw
    have hG2 := AtaB_bellman_value M hM M.gammaStar _ _ _ hmin
    rw [hdf w hwI] at hG2 ⊢
    rw [hθeq w hwI]
    simp only [Model.thetaStar]
    set y := M.vStar w
    have hc := ((lemma_2 M hM y).2 (M.a / 2 * y)).mpr rfl
    have hσ : 0 < M.σ := hM.2.2.2.2.2.2.2
    have hσ2 : 0 < M.σ ^ 2 := by positivity
    have hcost : M.cost (M.a / 2 * y) = y * (M.a / 2 * y) - M.a / 4 * y ^ 2 := by linarith
    rw [hcost, hG2]
    field_simp
    ring
  have h36 : derivWithin M.fStar s l = -M.kappa ∧ derivWithin M.fStar s u = 0 :=
    ⟨hBF.2.2.2.1, hBF.2.2.2.2.1⟩
  have hT := proposition_2 M hM P 𝔽 B hB l u M.gammaStar hlu θf hθc.measurable M.fStar hC2
    h35 h36 L U W hpol'
  refine hT.congr (fun t => ?_)
  simp only [Model.avgCost, Model.expCost]
  congr 2
  funext ω
  congr 1
  refine setLIntegral_congr_fun measurableSet_Icc (fun x hx => ?_)
  simp only [hWeq x ω hx.1]
