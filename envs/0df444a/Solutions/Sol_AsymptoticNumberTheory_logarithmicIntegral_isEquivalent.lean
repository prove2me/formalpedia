-- Prove2me | solution 1 for AsymptoticNumberTheory.logarithmicIntegral_isEquivalent
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T07:58:57.481985+00:00
-- url     : https://prove2.me/submissions/09f4dbf5-7a06-4f27-9985-645a834e3787

import Mathlib

open Filter Topology Asymptotics

lemma e4ff_cont (j : ℕ) : ContinuousOn (fun t : ℝ => (1 : ℝ) / (Real.log t) ^ j) (Set.Ici 2) := by
  apply ContinuousOn.div continuousOn_const
  · exact (Real.continuousOn_log.mono (fun t ht => by
      have : (2:ℝ) ≤ t := ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith)).pow j
  · intro t ht
    have h2 : (2:ℝ) ≤ t := ht
    have : 0 < Real.log t := Real.log_pos (by linarith)
    positivity

lemma e4ff_ii (j : ℕ) (a b : ℝ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ => (1 : ℝ) / (Real.log t) ^ j) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  refine (e4ff_cont j).mono ?_
  intro t ht
  rw [Set.mem_uIcc] at ht
  show (2:ℝ) ≤ t
  rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith

lemma e4ff_deriv (k : ℕ) (t : ℝ) (ht : 2 ≤ t) :
    HasDerivAt (fun t : ℝ => t / (Real.log t) ^ k)
      ((1 : ℝ) / (Real.log t) ^ k - (k : ℝ) * ((1 : ℝ) / (Real.log t) ^ (k + 1))) t := by
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  have hl : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log (by linarith)
  have hp : HasDerivAt (fun t : ℝ => Real.log t ^ k) ((k : ℝ) * Real.log t ^ (k - 1) * t⁻¹) t :=
    hl.pow k
  have := (hasDerivAt_id' t).div hp (pow_ne_zero _ hlt.ne')
  refine this.congr_deriv ?_
  have ht0 : t ≠ 0 := by linarith
  have hlt0 : Real.log t ≠ 0 := hlt.ne'
  cases k with
  | zero => simp
  | succ n =>
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

lemma e4ff_ftc (k : ℕ) (x : ℝ) (hx : 2 ≤ x) :
    x / (Real.log x) ^ k - 2 / (Real.log 2) ^ k =
      (∫ t in (2 : ℝ)..x, (1 : ℝ) / (Real.log t) ^ k)
        - (k : ℝ) * ∫ t in (2 : ℝ)..x, (1 : ℝ) / (Real.log t) ^ (k + 1) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => t / (Real.log t) ^ k)
    (f' := fun t : ℝ => (1 : ℝ) / (Real.log t) ^ k - (k : ℝ) * ((1 : ℝ) / (Real.log t) ^ (k + 1)))
    (a := 2) (b := x)
    (fun t ht => by
      rw [Set.uIcc_of_le hx] at ht
      exact e4ff_deriv k t ht.1)
    (((e4ff_ii k 2 x le_rfl hx)).sub (((e4ff_ii (k+1) 2 x le_rfl hx)).const_mul (k : ℝ)))
  rw [intervalIntegral.integral_sub (e4ff_ii k 2 x le_rfl hx)
    ((e4ff_ii (k+1) 2 x le_rfl hx).const_mul (k : ℝ)), intervalIntegral.integral_const_mul] at h
  linarith

lemma e4ff_Hbound (k : ℕ) (x : ℝ) (hx : 4 ≤ x) :
    ∫ t in (2 : ℝ)..x, (1 : ℝ) / (Real.log t) ^ (k + 1) ≤
      Real.sqrt x * ((1 : ℝ) / (Real.log 2) ^ (k + 1)) + x * (2 / Real.log x) ^ (k + 1) := by
  have hs2 : (2:ℝ) ≤ Real.sqrt x := by
    rw [show (2:ℝ) = Real.sqrt 4 by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have hsx : Real.sqrt x ≤ x := by
    have : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
    nlinarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (e4ff_ii (k+1) 2 (Real.sqrt x) le_rfl hs2) (e4ff_ii (k+1) (Real.sqrt x) x hs2 (by linarith))
  rw [← hsplit]
  have h1 : ∫ t in (2 : ℝ)..Real.sqrt x, (1 : ℝ) / (Real.log t) ^ (k + 1) ≤
      ∫ t in (2 : ℝ)..Real.sqrt x, (1 : ℝ) / (Real.log 2) ^ (k + 1) := by
    apply intervalIntegral.integral_mono_on hs2 (e4ff_ii (k+1) 2 (Real.sqrt x) le_rfl hs2)
      intervalIntegrable_const
    intro t ht
    have hl : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht.1
    apply one_div_le_one_div_of_le (pow_pos hl2 _)
    exact pow_le_pow_left₀ hl2.le hl _
  have hlsx : Real.log (Real.sqrt x) = Real.log x / 2 := by
    rw [Real.log_sqrt (by linarith)]
  have hlpos : 0 < Real.log (Real.sqrt x) := Real.log_pos (by linarith)
  have h2 : ∫ t in Real.sqrt x..x, (1 : ℝ) / (Real.log t) ^ (k + 1) ≤
      ∫ t in Real.sqrt x..x, (1 : ℝ) / (Real.log (Real.sqrt x)) ^ (k + 1) := by
    apply intervalIntegral.integral_mono_on (by linarith) (e4ff_ii (k+1) _ x hs2 (by linarith))
      intervalIntegrable_const
    intro t ht
    have hl : Real.log (Real.sqrt x) ≤ Real.log t := Real.log_le_log (by linarith) ht.1
    apply one_div_le_one_div_of_le (pow_pos hlpos _)
    exact pow_le_pow_left₀ hlpos.le hl _
  rw [intervalIntegral.integral_const] at h1 h2
  simp only [smul_eq_mul] at h1 h2
  have hlx : 0 < Real.log x := by rw [hlsx] at hlpos; linarith
  have e : (1 : ℝ) / (Real.log (Real.sqrt x)) ^ (k + 1) = (2 / Real.log x) ^ (k + 1) := by
    rw [hlsx, one_div, ← inv_pow]; congr 1; field_simp
  rw [e] at h2
  have hp : 0 ≤ (1 : ℝ) / (Real.log 2) ^ (k + 1) := by positivity
  have hq : 0 ≤ (2 / Real.log x) ^ (k + 1) := by positivity
  have a1 : (Real.sqrt x - 2) * ((1 : ℝ) / (Real.log 2) ^ (k + 1)) ≤
      Real.sqrt x * ((1 : ℝ) / (Real.log 2) ^ (k + 1)) := by nlinarith
  have a2 : (x - Real.sqrt x) * (2 / Real.log x) ^ (k + 1) ≤ x * (2 / Real.log x) ^ (k + 1) := by
    nlinarith
  linarith

lemma e4ff_alg (k : ℕ) (s L A c : ℝ) (hs : 0 < s) (hL : 0 < L) :
    ((k : ℝ) * (s * A + (s * s) * (2 / L) ^ (k + 1)) + c) / ((s * s) / L ^ k) =
      (k : ℝ) * (A * (L ^ k / s) + 2 ^ (k + 1) / L) + c * L ^ k / (s * s) := by
  rw [div_pow]
  field_simp
  ring

lemma e4ff_tend (k : ℕ) (A c : ℝ) :
    Tendsto (fun x : ℝ => (k : ℝ) * (A * (Real.log x ^ k / Real.sqrt x) + 2 ^ (k + 1) / Real.log x)
      + c * Real.log x ^ k / x) atTop (𝓝 0) := by
  have T3 : Tendsto (fun x : ℝ => Real.log x ^ k / x) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero
    simpa using this
  have T1 : Tendsto (fun x : ℝ => Real.log x ^ k / Real.sqrt x) atTop (𝓝 0) := by
    have h0 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero
    have h1 := (h0.comp Real.tendsto_sqrt_atTop).const_mul (2 ^ k)
    rw [mul_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    simp only [Function.comp, one_mul, add_zero]
    have : Real.log x = 2 * Real.log (Real.sqrt x) := by
      rw [Real.log_sqrt hx.le]; ring
    rw [this, mul_pow]
    have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
    field_simp
  have T2 : Tendsto (fun x : ℝ => (2:ℝ) ^ (k + 1) / Real.log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have := ((T1.const_mul A).add T2).const_mul (k : ℝ) |>.add (T3.const_mul c)
  simpa [mul_div_assoc] using this

open Filter Topology Asymptotics in
theorem solution (k : ℕ) (hk : 0 < k) :
    (fun x : ℝ => ∫ t in (2 : ℝ)..x, (1 : ℝ) / (Real.log t) ^ k) ~[atTop]
      (fun x : ℝ => x / (Real.log x) ^ k) := by
  set c : ℝ := 2 / (Real.log 2) ^ k with hc
  set A : ℝ := (1 : ℝ) / (Real.log 2) ^ (k + 1) with hA
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc0 : 0 ≤ c := by positivity
  show (fun x : ℝ => (∫ t in (2 : ℝ)..x, (1 : ℝ) / (Real.log t) ^ k) - x / (Real.log x) ^ k)
    =o[atTop] (fun x : ℝ => x / (Real.log x) ^ k)
  rw [Asymptotics.isLittleO_iff_tendsto']
  swap
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx h
    exfalso
    have : 0 < Real.log x := Real.log_pos hx
    have : 0 < x / (Real.log x) ^ k := by positivity
    linarith
  refine squeeze_zero_norm' ?_ (e4ff_tend k A c)
  filter_upwards [eventually_ge_atTop (4:ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hss : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hG : 0 < x / (Real.log x) ^ k := by positivity
  have hftc := e4ff_ftc k x (by linarith)
  have hHb := e4ff_Hbound k x hx
  have hH0 : 0 ≤ ∫ t in (2 : ℝ)..x, (1 : ℝ) / (Real.log t) ^ (k + 1) := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    have : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    positivity
  set H := ∫ t in (2 : ℝ)..x, (1 : ℝ) / (Real.log t) ^ (k + 1) with hH
  set F := ∫ t in (2 : ℝ)..x, (1 : ℝ) / (Real.log t) ^ k with hF
  have hFG : F - x / (Real.log x) ^ k = (k : ℝ) * H - c := by linarith
  rw [hFG, Real.norm_eq_abs, abs_div, abs_of_pos hG]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have habs : |(k : ℝ) * H - c| ≤ (k : ℝ) * (Real.sqrt x * A + x * (2 / Real.log x) ^ (k + 1)) + c := by
    rw [abs_le]
    constructor
    · have : 0 ≤ (k : ℝ) * H := by positivity
      have h2 : 0 ≤ (k : ℝ) * (Real.sqrt x * A + x * (2 / Real.log x) ^ (k + 1)) := by positivity
      linarith
    · have := mul_le_mul_of_nonneg_left hHb hk0
      linarith
  calc |(k : ℝ) * H - c| / (x / Real.log x ^ k)
      ≤ ((k : ℝ) * (Real.sqrt x * A + x * (2 / Real.log x) ^ (k + 1)) + c) / (x / Real.log x ^ k) :=
        div_le_div_of_nonneg_right habs hG.le
    _ = _ := by
        rw [← hss]
        have := e4ff_alg k (Real.sqrt x) (Real.log x) A c hs hlx
        rw [hss] at this ⊢
        exact this
