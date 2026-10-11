-- Prove2me | solution 1 for AsymptoticOperator.linearODE_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T23:20:56.714466+00:00
-- url     : https://prove2.me/submissions/490dbdd6-0768-43a3-be0e-c813e516ca22

import Mathlib.Analysis.ODE.ExistUnique

open Set Filter Topology Metric
open scoped NNReal

/-- For a continuous family `B : ℝ → (E →L[ℝ] E)` of bounded operators on a real Banach space
and any initial value `x₀`, the linear equation `x' = B(t) x` has exactly one solution
`x : ℝ → E` defined on all of `ℝ` with `x 0 = x₀`. -/
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (x₀ : E) :
    ∃! x : ℝ → E, x 0 = x₀ ∧ ∀ t, HasDerivAt x (B t (x t)) t := by
  -- bounds on compact intervals
  have bound : ∀ a b : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ‖B t‖ ≤ C := by
    intro a b
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hB.continuousOn
    exact ⟨max C 0, le_max_right _ _, fun t ht => (hC t ht).trans (le_max_left _ _)⟩
  -- uniqueness on open intervals
  have U : ∀ (a b t₀ : ℝ) (f g : ℝ → E), t₀ ∈ Ioo a b →
      (∀ t ∈ Ioo a b, HasDerivAt f (B t (f t)) t) →
      (∀ t ∈ Ioo a b, HasDerivAt g (B t (g t)) t) → f t₀ = g t₀ → EqOn f g (Ioo a b) := by
    intro a b t₀ f g ht hf hg heq
    obtain ⟨C, hC0, hC⟩ := bound a b
    refine ODE_solution_unique_of_mem_Ioo (v := fun t x => B t x) (s := fun _ => univ)
      (K := ⟨C, hC0⟩) (fun t ht' => ?_) ht (fun t ht' => ⟨hf t ht', trivial⟩)
      (fun t ht' => ⟨hg t ht', trivial⟩) heq
    refine ((B t).lipschitz.weaken ?_).lipschitzOnWith
    change ‖B t‖ ≤ C
    exact hC t (Ioo_subset_Icc_self ht')
  -- local existence with a uniform step on bounded sets of centres
  have L : ∀ T : ℝ, ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ ∀ s ∈ Icc (-T) T, ∀ x : E, ∃ y : ℝ → E, y s = x ∧
      ∀ t ∈ Ioo (s - h) (s + h), HasDerivAt y (B t (y t)) t := by
    intro T
    obtain ⟨C, hC0, hC⟩ := bound (-T - 1) (T + 1)
    refine ⟨1 / (2 * C + 2), by positivity, ?_, ?_⟩
    · rw [div_le_one (by positivity)]; linarith
    intro s hs x
    set h := 1 / (2 * C + 2) with hh
    have hpos : 0 < h := by positivity
    have hh1 : h ≤ 1 := by rw [hh, div_le_one (by positivity)]; linarith
    have hs0 : s ∈ Icc (s - h) (s + h) := ⟨by linarith, by linarith⟩
    have hsub : Icc (s - h) (s + h) ⊆ Icc (-T - 1) (T + 1) := by
      intro t ht; exact ⟨by linarith [hs.1, ht.1], by linarith [hs.2, ht.2]⟩
    have hPL : IsPicardLindelof (fun t y => B t y) (⟨s, hs0⟩ : Icc (s - h) (s + h)) x
        ⟨‖x‖ + 1, by positivity⟩ 0 ⟨C * (2 * ‖x‖ + 1), by positivity⟩ ⟨C, hC0⟩ := by
      refine ⟨fun t ht => ?_, fun y _ => ?_, fun t ht y hy => ?_, ?_⟩
      · refine ((B t).lipschitz.weaken ?_).lipschitzOnWith
        change ‖B t‖ ≤ C
        exact hC t (hsub ht)
      · exact ((hB.clm_apply continuous_const).continuousOn)
      · change ‖B t y‖ ≤ C * (2 * ‖x‖ + 1)
        have hy' : ‖y‖ ≤ 2 * ‖x‖ + 1 := by
          have h3 : dist y x ≤ ‖x‖ + 1 := mem_closedBall.mp hy
          have h2 := norm_le_insert' y x
          rw [← dist_eq_norm] at h2
          linarith
        calc ‖B t y‖ ≤ ‖B t‖ * ‖y‖ := (B t).le_opNorm y
          _ ≤ C * (2 * ‖x‖ + 1) :=
            mul_le_mul (hC t (hsub ht)) hy' (norm_nonneg _) hC0
      · simp only [NNReal.coe_mk]
        have hm : max (s + h - s) (s - (s - h)) = h := by
          rw [show s + h - s = h by ring, show s - (s - h) = h by ring, max_self]
        rw [hm, hh]
        rw [mul_one_div, div_le_iff₀ (by positivity)]
        have e0 : ((0 : ℝ≥0) : ℝ) = 0 := rfl
        rw [e0]
        change C * (2 * ‖x‖ + 1) ≤ (‖x‖ + 1 - 0) * (2 * C + 2)
        nlinarith [norm_nonneg x]
    obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    refine ⟨α, hα0, fun t ht => ?_⟩
    exact (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  -- gluing two solutions that agree on an overlap
  have G : ∀ (a b c d : ℝ) (y z : ℝ → E), a < b → c < b → b ≤ d →
      (∀ t ∈ Ioo a b, HasDerivAt y (B t (y t)) t) →
      (∀ t ∈ Ioo c d, HasDerivAt z (B t (z t)) t) → EqOn y z (Ioo (max a c) b) →
      ∃ w : ℝ → E, (∀ t ∈ Ioo a d, HasDerivAt w (B t (w t)) t) ∧ EqOn w y (Ioo a b) ∧
        EqOn w z (Ioo (max a c) d) := by
    intro a b c d y z hab hcb hbd hy hz hyz
    refine ⟨fun t => if t < b then y t else z t, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
    · by_cases htb : t < b
      · have hev : (fun t => if t < b then y t else z t) =ᶠ[𝓝 t] y := by
          filter_upwards [Iio_mem_nhds htb] with u hu
          simp [show u < b from hu]
        have := (hy t ⟨ht.1, htb⟩).congr_of_eventuallyEq hev
        simpa [htb] using this
      · have hct : c < t := lt_of_lt_of_le hcb (not_lt.mp htb)
        have hev : (fun t => if t < b then y t else z t) =ᶠ[𝓝 t] z := by
          filter_upwards [Ioi_mem_nhds (show max a c < t from max_lt ht.1 hct)] with u hu
          by_cases hub : u < b
          · simp only [hub, if_true]; exact hyz ⟨hu, hub⟩
          · simp [hub]
        have := (hz t ⟨hct, ht.2⟩).congr_of_eventuallyEq hev
        simpa [htb] using this
    · simp [ht.2]
    · by_cases htb : t < b
      · simp only [htb, if_true]; exact hyz ⟨ht.1, htb⟩
      · simp [htb]
  -- existence on every symmetric interval
  have Ex : ∀ T : ℝ, ∃ y : ℝ → E, y 0 = x₀ ∧ ∀ t ∈ Ioo (-T) T, HasDerivAt y (B t (y t)) t := by
    intro T
    obtain ⟨h, hpos, hh1, hloc⟩ := L (|T| + 1)
    have P : ∀ N : ℕ, (N : ℝ) * (h / 2) ≤ |T| + 1 → ∃ y : ℝ → E, y 0 = x₀ ∧
        ∀ t ∈ Ioo (-((N + 1) * (h / 2))) ((N + 1) * (h / 2)), HasDerivAt y (B t (y t)) t := by
      intro N
      induction N with
      | zero =>
        intro _
        obtain ⟨y, hy0, hy⟩ := hloc 0 ⟨by linarith [abs_nonneg T], by linarith [abs_nonneg T]⟩ x₀
        refine ⟨y, hy0, fun t ht => hy t ⟨?_, ?_⟩⟩
        · simp at ht; linarith [ht.1]
        · simp at ht; linarith [ht.2]
      | succ N ih =>
        intro hN
        push_cast at hN
        obtain ⟨y, hy0, hy⟩ := ih (by nlinarith)
        set r : ℝ := (N + 1) * (h / 2) with hr
        have hr0 : h / 2 ≤ r := by rw [hr]; nlinarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]
        set s : ℝ := r - h / 2 with hs
        have hs0 : 0 ≤ s := by linarith
        have hsT : s ≤ |T| + 1 := by rw [hs, hr]; nlinarith
        -- right extension
        obtain ⟨z, hz0, hz⟩ := hloc s ⟨by linarith [abs_nonneg T], hsT⟩ (y s)
        have hyz : EqOn y z (Ioo (max (-r) (s - h)) r) :=
          U _ _ s y z ⟨max_lt (by linarith) (by linarith), by linarith⟩
            (fun t ht => hy t ⟨(le_max_left _ _).trans_lt ht.1, ht.2⟩)
            (fun t ht => hz t ⟨(le_max_right _ _).trans_lt ht.1, by linarith [ht.2]⟩) hz0.symm
        obtain ⟨w, hw, hwy, -⟩ := G (-r) r (s - h) (s + h) y z (by linarith) (by linarith)
          (by linarith) hy hz hyz
        -- left extension
        have hsT' : -s ∈ Icc (-(|T| + 1)) (|T| + 1) := ⟨by linarith, by linarith⟩
        obtain ⟨z', hz'0, hz'⟩ := hloc (-s) hsT' (w (-s))
        have hz'w : EqOn z' w (Ioo (max (-s - h) (-r)) (-s + h)) :=
          U _ _ (-s) z' w ⟨max_lt (by linarith) (by linarith), by linarith⟩
            (fun t ht => hz' t ⟨(le_max_left _ _).trans_lt ht.1, ht.2⟩)
            (fun t ht => hw t ⟨(le_max_right _ _).trans_lt ht.1, by linarith [ht.2]⟩) hz'0
        obtain ⟨w', hw', -, hw'w⟩ := G (-s - h) (-s + h) (-r) (s + h) z' w (by linarith)
          (by linarith) (by linarith) hz' hw hz'w
        refine ⟨w', ?_, fun t ht => hw' t ⟨?_, ?_⟩⟩
        · rw [hw'w ⟨max_lt (by linarith) (by linarith), by linarith⟩,
            hwy ⟨by linarith, by linarith⟩, hy0]
        · have := ht.1; push_cast at this; linarith
        · have := ht.2; push_cast at this; linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * (|T| + 1) / h)
    -- choose the least admissible step count
    classical
    let N₀ := Nat.find (⟨N, hN⟩ : ∃ N : ℕ, 2 * (|T| + 1) / h < N)
    have hN₀ : 2 * (|T| + 1) / h < N₀ := Nat.find_spec (⟨N, hN⟩ : ∃ N : ℕ, 2 * (|T| + 1) / h < N)
    have hN₀pos : 0 < N₀ := by
      have : (0 : ℝ) < N₀ := lt_of_le_of_lt (by positivity) hN₀
      exact_mod_cast this
    obtain ⟨M, hM⟩ : ∃ M, N₀ = M + 1 := ⟨N₀ - 1, by omega⟩
    have hMle : ¬ (2 * (|T| + 1) / h < M) := Nat.find_min _ (by omega : M < N₀)
    push_neg at hMle
    have hMb : (M : ℝ) * (h / 2) ≤ |T| + 1 := by
      rw [le_div_iff₀ hpos] at hMle; linarith
    obtain ⟨y, hy0, hy⟩ := P M hMb
    refine ⟨y, hy0, fun t ht => hy t ⟨?_, ?_⟩⟩
    · have h1 : 2 * (|T| + 1) < (M + 1 : ℝ) * h := by
        have := hN₀; rw [hM, div_lt_iff₀ hpos] at this; push_cast at this; linarith
      have := ht.1; have := le_abs_self T; nlinarith
    · have h1 : 2 * (|T| + 1) < (M + 1 : ℝ) * h := by
        have := hN₀; rw [hM, div_lt_iff₀ hpos] at this; push_cast at this; linarith
      have := ht.2; have := le_abs_self T; nlinarith
  choose Y hY0 hY using Ex
  -- global solution
  have agree : ∀ T₁ T₂ u, |u| < T₁ → |u| < T₂ → Y T₁ u = Y T₂ u := by
    intro T₁ T₂ u h1 h2
    have hm : |u| < min T₁ T₂ := lt_min h1 h2
    refine U (-(min T₁ T₂)) (min T₁ T₂) 0 (Y T₁) (Y T₂) ⟨?_, ?_⟩
      (fun t ht => hY T₁ t ⟨?_, ?_⟩) (fun t ht => hY T₂ t ⟨?_, ?_⟩) (by rw [hY0, hY0]) ?_
    all_goals first
      | (have := abs_nonneg u; linarith [min_le_left T₁ T₂, min_le_right T₁ T₂])
      | (linarith [ht.1, ht.2, min_le_left T₁ T₂, min_le_right T₁ T₂])
      | exact ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
  refine ⟨fun t => Y (|t| + 1) t, ⟨?_, fun t => ?_⟩, ?_⟩
  · simp only; exact hY0 _
  · have hev : (fun u => Y (|u| + 1) u) =ᶠ[𝓝 t] Y (|t| + 1) := by
      have hc : Continuous fun u : ℝ => |u| := continuous_abs
      filter_upwards [hc.continuousAt.eventually (Iio_mem_nhds (show |t| < |t| + 1 by linarith))]
        with u hu
      exact agree _ _ u (by linarith) hu
    have hd := (hY (|t| + 1) t ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩)
    have := hd.congr_of_eventuallyEq hev
    simpa [agree (|t| + 1) (|t| + 1) t (by linarith) (by linarith)] using this
  · rintro Ψ ⟨hΨ0, hΨ⟩
    funext t
    have h1 := U (-(|t| + 1)) (|t| + 1) 0 Ψ (Y (|t| + 1))
      ⟨by linarith [abs_nonneg t], by linarith [abs_nonneg t]⟩
      (fun u _ => hΨ u) (fun u hu => hY _ u hu) (by rw [hΨ0, hY0])
    exact h1 ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩

