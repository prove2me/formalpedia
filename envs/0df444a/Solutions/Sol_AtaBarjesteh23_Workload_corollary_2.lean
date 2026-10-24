-- Prove2me | solution 1 for AtaBarjesteh23.Workload.corollary_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T20:42:31.877053+00:00
-- url     : https://prove2.me/submissions/4c4c249a-38a3-4150-a9cd-638232a365af

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting
import Definitions.Def_AtaBarjesteh23_Workload_DriftBM
import Definitions.Def_AtaBarjesteh23_Workload_Control
import Theorems.Thm_AtaBarjesteh23_Workload_proposition_3
import Theorems.Thm_AtaBarjesteh23_Workload_lemma_2

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

theorem AtaB_bellman_deriv (M : Model) (hM : M.Standing) {l u γ : ℝ} {v : ℝ → ℝ}
    (hv : M.BellmanV l u γ v) :
    ∀ w ∈ Icc l u, HasDerivWithinAt v (M.a / (2 * M.σ ^ 2) * v w ^ 2 - 2 * M.μ / M.σ ^ 2 * v w
      + 2 * (γ - M.hcost w) / M.σ ^ 2) (Icc l u) w := by
  obtain ⟨hlu, hC1, hode, -, -, -, -⟩ := hv
  have hhcont : Continuous M.hcost := (AtaB_basic M hM).2.2.2.2.2.2.2.2
  have hUD : UniqueDiffOn ℝ (Icc l u) := uniqueDiffOn_Icc hlu
  have hRcont : ContinuousOn (fun w => M.a / (2 * M.σ ^ 2) * v w ^ 2 - 2 * M.μ / M.σ ^ 2 * v w
      + 2 * (γ - M.hcost w) / M.σ ^ 2) (Icc l u) := by
    have := hC1.continuousOn
    have := hhcont.continuousOn (s := Icc l u)
    fun_prop
  have hEq : EqOn (derivWithin v (Icc l u)) (fun w => M.a / (2 * M.σ ^ 2) * v w ^ 2
      - 2 * M.μ / M.σ ^ 2 * v w + 2 * (γ - M.hcost w) / M.σ ^ 2) (Icc l u) := by
    refine EqOn.of_subset_closure (s := Ioo l u) ?_ (hC1.continuousOn_derivWithin hUD le_rfl)
      hRcont Ioo_subset_Icc_self (by rw [closure_Ioo hlu.ne])
    intro w hw
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hw.1 hw.2)]
    exact hode w hw
  intro w hw
  have := ((hC1.differentiableOn (by norm_num)) w hw).hasDerivWithinAt
  rwa [hEq hw] at this

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
theorem solution (M : Model) (hM : M.Standing) :
    StrictAntiOn M.fStar (Icc M.lStar M.uStar) ∧
    StrictConvexOn ℝ (Icc M.lStar M.uStar) M.fStar ∧
    ContDiffOn ℝ 2 M.fStar (Icc M.lStar M.uStar) ∧
    M.BellmanF M.lStar M.uStar M.gammaStar M.fStar ∧
    ∀ (l u γ : ℝ) (g : ℝ → ℝ), M.BellmanF l u γ g →
      l = M.lStar ∧ u = M.uStar ∧ γ = M.gammaStar ∧
        ∃ C : ℝ, ∀ w ∈ Icc l u, g w = M.fStar w + C := by
  obtain ⟨hneg, hmono, hC1, hBV, huniq⟩ := proposition_3 M hM
  have hBV' := hBV
  obtain ⟨hlu, -, -, hvl, hvu, hdl, hdu⟩ := hBV'
  have hR := AtaB_bellman_deriv M hM hBV
  set s := Icc M.lStar M.uStar with hs
  have hUD : UniqueDiffOn ℝ s := uniqueDiffOn_Icc hlu
  have hfd := AtaB_f_deriv M hM
  have hdf : ∀ w ∈ s, derivWithin M.fStar s w = M.vStar w := fun w hw =>
    (hfd w hw).derivWithin (hUD w hw)
  have hdv : ∀ w ∈ s, derivWithin M.vStar s w = M.a / (2 * M.σ ^ 2) * M.vStar w ^ 2
      - 2 * M.μ / M.σ ^ 2 * M.vStar w + 2 * (M.gammaStar - M.hcost w) / M.σ ^ 2 :=
    fun w hw => (hR w hw).derivWithin (hUD w hw)
  have hd2 : ∀ w ∈ s, iteratedDerivWithin 2 M.fStar s w = derivWithin M.vStar s w := by
    intro w hw
    rw [AtaB_iter2]
    exact derivWithin_congr (fun x hx => hdf x hx) (hdf w hw)
  have hfc : ContinuousOn M.fStar s := fun w hw => (hfd w hw).continuousWithinAt
  have hC2 : ContDiffOn ℝ 2 M.fStar s := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_derivWithin hUD]
    refine ⟨fun w hw => (hfd w hw).differentiableWithinAt, by simp, ?_⟩
    exact hC1.congr (fun x hx => hdf x hx)
  have hvneg : ∀ w ∈ Ioo M.lStar M.uStar, M.vStar w < 0 := by
    intro w hw
    have := hmono ⟨hw.1.le, hw.2.le⟩ ⟨hlu.le, le_rfl⟩ hw.2
    rwa [hvu] at this
  refine ⟨?_, ?_, hC2, ?_, ?_⟩
  · refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _) hfc (f' := M.vStar) ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx ⊢
      exact (hfd x (Ioo_subset_Icc_self hx)).mono Ioo_subset_Icc_self
    · intro x hx
      rw [interior_Icc] at hx
      exact hvneg x hx
  · refine StrictMonoOn.strictConvexOn_of_deriv (convex_Icc _ _) hfc ?_
    rw [interior_Icc]
    intro x hx y hy hxy
    rw [((hfd x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)).deriv,
      ((hfd y (Ioo_subset_Icc_self hy)).hasDerivAt (Icc_mem_nhds hy.1 hy.2)).deriv]
    exact hmono (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy) hxy
  · refine ⟨hlu, hC2, ?_, ?_, ?_, ?_, ?_⟩
    · intro w hw
      have hwI : w ∈ s := Ioo_subset_Icc_self hw
      rw [hd2 w hwI, hdf w hwI, hdv w hwI]
      set y := M.vStar w
      have hσ := (AtaB_basic M hM).2.2.2.2.2.1
      have hσ2 : 0 < M.σ ^ 2 := by positivity
      have hE : ∀ x, M.σ ^ 2 / 2 * (M.a / (2 * M.σ ^ 2) * y ^ 2 - 2 * M.μ / M.σ ^ 2 * y
          + 2 * (M.gammaStar - M.hcost w) / M.σ ^ 2) + M.μ * y - x * y + M.cost x + M.hcost w
          = M.gammaStar + (M.a / 4 * y ^ 2 - (y * x - M.cost x)) := by
        intro x; field_simp; ring
      obtain ⟨⟨⟨x0, hx0⟩, hmax⟩, -⟩ := lemma_2 M hM y
      refine ⟨⟨x0, ?_⟩, ?_⟩
      · simp only at hx0 ⊢; rw [hE, hx0]; ring
      · rintro _ ⟨x, rfl⟩
        simp only
        rw [hE]
        have := hmax ⟨x, rfl⟩
        simp only at this
        linarith
    · rw [hdf _ ⟨le_rfl, hlu.le⟩, hvl]
    · rw [hdf _ ⟨hlu.le, le_rfl⟩, hvu]
    · rw [hd2 _ ⟨le_rfl, hlu.le⟩, hdl]
    · rw [hd2 _ ⟨hlu.le, le_rfl⟩, hdu]
  · intro l u γ g hg
    obtain ⟨hlu', hC2g, hmin, hgl, hgu, hg2l, hg2u⟩ := hg
    set s' := Icc l u with hs'
    have hUD' : UniqueDiffOn ℝ s' := uniqueDiffOn_Icc hlu'
    rw [AtaB_iter2] at hg2l hg2u
    have hC2g' := hC2g
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_derivWithin hUD'] at hC2g'
    obtain ⟨hgdiff, -, hC1v⟩ := hC2g'
    have hBVg : M.BellmanV l u γ (derivWithin g s') := by
      refine ⟨hlu', hC1v, ?_, hgl, hgu, hg2l, hg2u⟩
      intro w hw
      have h := hmin w hw
      rw [AtaB_iter2] at h
      rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hw.1 hw.2)]
      exact AtaB_bellman_value M hM γ _ _ _ h
    obtain ⟨hl, hu, hγ, hEq⟩ := huniq l u γ _ hBVg
    refine ⟨hl, hu, hγ, g l - M.fStar l, ?_⟩
    have hss : s' = s := by rw [hs', hs, hl, hu]
    have hdiff : DifferentiableOn ℝ (fun w => g w - M.fStar w) s' := by
      intro w hw
      have hw' : w ∈ s := hss ▸ hw
      exact (hgdiff w hw).sub ((hfd w hw').differentiableWithinAt.mono hss.subset)
    have hzero : ∀ x ∈ Ico l u, derivWithin (fun w => g w - M.fStar w) s' x = 0 := by
      intro x hx
      have hxI : x ∈ s' := Ico_subset_Icc_self hx
      have hx' : x ∈ s := hss ▸ hxI
      have h1 := (hgdiff x hxI).hasDerivWithinAt
      have h2 := (hfd x hx').mono hss.subset
      have h3 : HasDerivWithinAt (fun w => g w - M.fStar w)
          (derivWithin g s' x - M.vStar x) s' x := h1.sub h2
      rw [h3.derivWithin (hUD' x hxI), hEq hxI, sub_self]
    intro w hw
    have := constant_of_derivWithin_zero hdiff hzero w hw
    linarith
