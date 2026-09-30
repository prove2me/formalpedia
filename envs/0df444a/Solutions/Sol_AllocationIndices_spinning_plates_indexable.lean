-- Prove2me | solution 1 for AllocationIndices.spinning_plates_indexable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T03:12:29.728237+00:00
-- url     : https://prove2.me/submissions/3dd6c11c-8991-49d6-bc9b-12eef0897ddc

import Mathlib
import Definitions.Def_AllocationIndices_Restless

set_option autoImplicit false

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p4259_prob {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : IsProbabilityMeasure (markovChainMeasure P x) := by
  unfold markovChainMeasure; infer_instance

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p4259_marg0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : (markovChainMeasure P x).map (Preorder.frestrictLe 0) =
      Measure.dirac (fun _ ↦ x) := by
  rw [markovChainMeasure, Kernel.trajMeasure,
    Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_dirac' (MeasurableEquiv.measurable _)]
  congr 1

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p4259_int0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) (F : S → ℝ) (hF : Measurable F) :
    ∫ ω, F (ω 0) ∂markovChainMeasure P x = F x := by
  have hFm : Measurable (fun h : (Π _i : Finset.Iic 0, S) ↦ F (h ⟨0, Finset.mem_Iic.2 le_rfl⟩)) :=
    hF.comp (measurable_pi_apply _)
  have h1 := integral_map (μ := markovChainMeasure P x) (Preorder.measurable_frestrictLe 0).aemeasurable
    hFm.aestronglyMeasurable
  rw [p4259_marg0, integral_dirac' _ _ hFm.stronglyMeasurable] at h1
  exact h1.symm

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p4259_int_of_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (F : α → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ x, |F x| ≤ B) :
    Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p4259_step {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) (s : ℕ) (g : S → ℝ) (Bg : ℝ)
    (hg : ∀ y, |g y| ≤ Bg) :
    ∫ ω, g (ω (s + 1)) ∂markovChainMeasure P x =
      ∫ ω, (∫ z, g z ∂P (ω s)) ∂markovChainMeasure P x := by
  have := p4259_prob P x
  have hgm : Measurable g := Measurable.of_discrete
  have hPgm : Measurable (fun y ↦ ∫ z, g z ∂P y) := Measurable.of_discrete
  have hmap : (markovChainMeasure P x).map (Preorder.frestrictLe s) ⊗ₘ markovChainStep P s =
      (markovChainMeasure P x).map (fun ω ↦ (Preorder.frestrictLe s ω, ω (s + 1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure (X := fun _ : ℕ ↦ S)
      (μ₀ := Measure.dirac x) (κ := markovChainStep P) (a := s)
  have hΦ : Measurable (fun ω : ℕ → S ↦ (Preorder.frestrictLe s ω, ω (s + 1))) :=
    (Preorder.measurable_frestrictLe s).prodMk (measurable_pi_apply (s + 1))
  have hFm : Measurable (fun p : (Π _i : Finset.Iic s, S) × S ↦ g p.2) :=
    hgm.comp measurable_snd
  have hFint : Integrable (fun p : (Π _i : Finset.Iic s, S) × S ↦ g p.2)
      ((markovChainMeasure P x).map (Preorder.frestrictLe s) ⊗ₘ markovChainStep P s) :=
    p4259_int_of_bound _ _ hFm Bg (fun p ↦ hg _)
  have hGm : Measurable
      (fun h : (Π _i : Finset.Iic s, S) ↦ ∫ z, g z ∂P (h ⟨s, Finset.mem_Iic.2 le_rfl⟩)) :=
    hPgm.comp (measurable_pi_apply _)
  calc ∫ ω, g (ω (s + 1)) ∂markovChainMeasure P x
      = ∫ ω, (fun p : (Π _i : Finset.Iic s, S) × S ↦ g p.2)
          (Preorder.frestrictLe s ω, ω (s + 1)) ∂markovChainMeasure P x := rfl
    _ = ∫ p, (fun p : (Π _i : Finset.Iic s, S) × S ↦ g p.2) p
          ∂((markovChainMeasure P x).map (fun ω ↦ (Preorder.frestrictLe s ω, ω (s + 1)))) :=
        (integral_map hΦ.aemeasurable hFm.aestronglyMeasurable).symm
    _ = ∫ p, (fun p : (Π _i : Finset.Iic s, S) × S ↦ g p.2) p
          ∂((markovChainMeasure P x).map (Preorder.frestrictLe s) ⊗ₘ markovChainStep P s) := by
        rw [hmap]
    _ = ∫ h, ∫ y, (fun p : (Π _i : Finset.Iic s, S) × S ↦ g p.2) (h, y) ∂(markovChainStep P s h)
          ∂((markovChainMeasure P x).map (Preorder.frestrictLe s)) :=
        Measure.integral_compProd hFint
    _ = ∫ h, (fun h : (Π _i : Finset.Iic s, S) ↦ ∫ z, g z ∂P (h ⟨s, Finset.mem_Iic.2 le_rfl⟩)) h
          ∂((markovChainMeasure P x).map (Preorder.frestrictLe s)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun h ↦ ?_)
        have hk : markovChainStep P s h = P (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) := by
          rw [markovChainStep, Kernel.comap_apply]
        simp only
        rw [hk]
    _ = ∫ ω, (fun h : (Π _i : Finset.Iic s, S) ↦ ∫ z, g z ∂P (h ⟨s, Finset.mem_Iic.2 le_rfl⟩))
          (Preorder.frestrictLe s ω) ∂markovChainMeasure P x :=
        integral_map (Preorder.measurable_frestrictLe s).aemeasurable hGm.aestronglyMeasurable
    _ = ∫ ω, (∫ z, g z ∂P (ω s)) ∂markovChainMeasure P x := rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset Filter in
private lemma p4259_avg {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Fintype S]
    (P : Kernel S S) [IsMarkovKernel P] (f c h : S → ℝ)
    (hc : ∀ z, ∫ y, c y ∂P z = c z) (hh : ∀ z, f z + ∫ y, h y ∂P z = c z + h z) (x : S) :
    limsup (fun T : ℕ ↦ (T : ℝ)⁻¹ * ∑ t ∈ range T, ∫ ω, f (ω t) ∂markovChainMeasure P x)
      atTop = c x := by
  have := p4259_prob P x
  have hbd : ∀ u : S → ℝ, ∀ y, |u y| ≤ ∑ z, |u z| := fun u y ↦
    Finset.single_le_sum (f := fun z ↦ |u z|) (fun z _ ↦ abs_nonneg _) (Finset.mem_univ y)
  have hint : ∀ (u : S → ℝ) (t : ℕ),
      Integrable (fun ω : ℕ → S ↦ u (ω t)) (markovChainMeasure P x) := fun u t ↦
    p4259_int_of_bound _ _ ((Measurable.of_discrete (f := u)).comp (measurable_pi_apply t)) _
      (fun ω ↦ hbd u (ω t))
  have hstep : ∀ (u : S → ℝ) (t : ℕ), ∫ ω, u (ω (t + 1)) ∂markovChainMeasure P x =
      ∫ ω, (∫ y, u y ∂P (ω t)) ∂markovChainMeasure P x := fun u t ↦
    p4259_step P x t u _ (hbd u)
  have hc' : ∀ t, ∫ ω, c (ω t) ∂markovChainMeasure P x = c x := by
    intro t
    induction t with
    | zero => exact p4259_int0 P x c Measurable.of_discrete
    | succ t ih =>
      rw [hstep, ← ih]
      exact integral_congr_ae (Eventually.of_forall fun ω ↦ hc (ω t))
  have hf' : ∀ t, ∫ ω, f (ω t) ∂markovChainMeasure P x =
      c x + ∫ ω, h (ω t) ∂markovChainMeasure P x - ∫ ω, h (ω (t + 1)) ∂markovChainMeasure P x := by
    intro t
    rw [hstep h t, ← hc' t, ← integral_add (hint c t) (hint h t),
      ← integral_sub (show Integrable (fun ω : ℕ → S ↦ c (ω t) + h (ω t)) (markovChainMeasure P x)
        from (hint c t).add (hint h t)) (hint (fun z ↦ ∫ y, h y ∂P z) t)]
    refine integral_congr_ae (Eventually.of_forall fun ω ↦ ?_)
    have := hh (ω t)
    simp only
    linarith
  have hsum : ∀ T : ℕ, ∑ t ∈ range T, ∫ ω, f (ω t) ∂markovChainMeasure P x =
      T * c x + (h x - ∫ ω, h (ω T) ∂markovChainMeasure P x) := by
    intro T
    induction T with
    | zero => simp [p4259_int0 P x h Measurable.of_discrete]
    | succ T ih => rw [sum_range_succ, ih, hf']; push_cast; ring
  set B := ∑ z, |h z| with hB
  have he : ∀ T : ℕ, |h x - ∫ ω, h (ω T) ∂markovChainMeasure P x| ≤ 2 * B := by
    intro T
    have h1 : |∫ ω, h (ω T) ∂markovChainMeasure P x| ≤ B := by
      have := norm_integral_le_of_norm_le_const (μ := markovChainMeasure P x)
        (f := fun ω : ℕ → S ↦ h (ω T)) (C := B)
        (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hbd h (ω T))
      rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
    have h2 := hbd h x
    calc _ ≤ |h x| + |∫ ω, h (ω T) ∂markovChainMeasure P x| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  have hlim : Tendsto (fun T : ℕ ↦ c x + (T : ℝ)⁻¹ *
      (h x - ∫ ω, h (ω T) ∂markovChainMeasure P x)) atTop (nhds (c x)) := by
    have h0 : Tendsto (fun T : ℕ ↦ (T : ℝ)⁻¹ *
        (h x - ∫ ω, h (ω T) ∂markovChainMeasure P x)) atTop (nhds 0) := by
      refine squeeze_zero_norm (fun T ↦ ?_) (tendsto_const_div_atTop_nhds_zero_nat (2 * B))
      rw [Real.norm_eq_abs, abs_mul, abs_inv, Nat.abs_cast, inv_mul_eq_div]
      exact div_le_div_of_nonneg_right (he T) (Nat.cast_nonneg T)
    simpa using h0.const_add (c x)
  refine Tendsto.limsup_eq (hlim.congr' ?_)
  filter_upwards [eventually_ge_atTop 1] with T hT
  rw [hsum T]
  have hT' : (T : ℝ) ≠ 0 := by positivity
  field_simp

private def p4259_G {k : ℕ} (g : Fin k → Bool) (j : ℕ) : Bool :=
  if h : j < k then g ⟨j, h⟩ else false

private lemma p4259_G_ge {k : ℕ} (g : Fin k → Bool) (j : ℕ) (hj : k ≤ j) :
    p4259_G g j = false := by
  unfold p4259_G; rw [dif_neg (by omega)]

private lemma p4259_G_fin {k : ℕ} (g : Fin k → Bool) (z : Fin k) : p4259_G g z.val = g z := by
  unfold p4259_G; rw [dif_pos z.isLt]

private lemma p4259_ex {k : ℕ} (g : Fin k → Bool) (z : ℕ) :
    ∃ j, z < j ∧ p4259_G g j = false :=
  ⟨z + k + 1, by omega, p4259_G_ge g _ (by omega)⟩

private noncomputable def p4259_Lup {k : ℕ} (g : Fin k → Bool) (z : ℕ) : ℕ :=
  Nat.find (p4259_ex g z)

private lemma p4259_Lup_spec {k : ℕ} (g : Fin k → Bool) (z : ℕ) :
    z < p4259_Lup g z ∧ p4259_G g (p4259_Lup g z) = false :=
  Nat.find_spec (p4259_ex g z)

private lemma p4259_Lup_min {k : ℕ} (g : Fin k → Bool) (z j : ℕ) (hj : z < j)
    (hg : p4259_G g j = false) : p4259_Lup g z ≤ j :=
  Nat.find_min' (p4259_ex g z) ⟨hj, hg⟩

private def p4259_Ldown {k : ℕ} (g : Fin k → Bool) (z : ℕ) : ℕ :=
  Nat.findGreatest (fun y ↦ 0 < y ∧ p4259_G g (y - 1) = true) z

private noncomputable def p4259_L {k : ℕ} (g : Fin k → Bool) (z : ℕ) : ℕ :=
  if p4259_G g z = true then p4259_Lup g z else p4259_Ldown g z

private lemma p4259_L_up {k : ℕ} (g : Fin k → Bool) (z : ℕ) (hz : p4259_G g z = true)
    (_hk : z + 1 < k) : p4259_L g (z + 1) = p4259_L g z := by
  have hLz : p4259_L g z = p4259_Lup g z := by unfold p4259_L; rw [if_pos hz]
  rw [hLz]
  obtain ⟨s1, s2⟩ := p4259_Lup_spec g z
  cases h1 : p4259_G g (z + 1) with
  | false =>
    have e1 : p4259_L g (z + 1) = z + 1 := by
      unfold p4259_L; rw [if_neg (by simp [h1])]
      unfold p4259_Ldown
      exact Nat.findGreatest_eq ⟨by omega, by simpa using hz⟩
    have := p4259_Lup_min g z (z + 1) (by omega) h1
    omega
  | true =>
    have e1 : p4259_L g (z + 1) = p4259_Lup g (z + 1) := by unfold p4259_L; rw [if_pos h1]
    rw [e1]
    obtain ⟨t1, t2⟩ := p4259_Lup_spec g (z + 1)
    have a1 := p4259_Lup_min g z _ (by omega) t2
    have hne : p4259_Lup g z ≠ z + 1 := by
      intro he; rw [he, h1] at s2; exact absurd s2 (by decide)
    have a2 := p4259_Lup_min g (z + 1) _ (by omega) s2
    omega

private lemma p4259_L_pair {k : ℕ} (g : Fin k → Bool) (m : ℕ) (hm : p4259_G g m = true)
    (hm1 : p4259_G g (m + 1) = false) : p4259_L g (m + 1) = m + 1 := by
  unfold p4259_L; rw [if_neg (by simp [hm1])]
  unfold p4259_Ldown
  exact Nat.findGreatest_eq ⟨by omega, by simpa using hm⟩

private lemma p4259_L_dn {k : ℕ} (g : Fin k → Bool) (z : ℕ) (hz : p4259_G g z = false)
    (h0 : 0 < z) : p4259_L g (z - 1) = p4259_L g z := by
  obtain ⟨m, rfl⟩ : ∃ m, z = m + 1 := ⟨z - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  cases h1 : p4259_G g m with
  | true =>
    rw [p4259_L_pair g m h1 hz]
    have e1 : p4259_L g m = p4259_Lup g m := by unfold p4259_L; rw [if_pos h1]
    rw [e1]
    obtain ⟨s1, s2⟩ := p4259_Lup_spec g m
    have := p4259_Lup_min g m (m + 1) (by omega) hz
    omega
  | false =>
    have e1 : p4259_L g m = p4259_Ldown g m := by unfold p4259_L; rw [if_neg (by simp [h1])]
    have e2 : p4259_L g (m + 1) = p4259_Ldown g (m + 1) := by
      unfold p4259_L; rw [if_neg (by simp [hz])]
    rw [e1, e2]
    unfold p4259_Ldown
    rw [Nat.findGreatest_of_not]
    simp [h1]

private lemma p4259_L_top {k : ℕ} (g : Fin k → Bool) (z : ℕ) (hz : p4259_G g z = true)
    (hk : z + 1 = k) : p4259_L g z = k := by
  unfold p4259_L; rw [if_pos hz]
  obtain ⟨s1, s2⟩ := p4259_Lup_spec g z
  have := p4259_Lup_min g z k (by omega) (p4259_G_ge g k le_rfl)
  omega

private lemma p4259_L_zero {k : ℕ} (g : Fin k → Bool) (hz : p4259_G g 0 = false) :
    p4259_L g 0 = 0 := by
  unfold p4259_L; rw [if_neg (by simp [hz])]; unfold p4259_Ldown; exact Nat.findGreatest_zero

private lemma p4259_L_le {k : ℕ} (g : Fin k → Bool) (z : ℕ) (hz : z < k) : p4259_L g z ≤ k := by
  unfold p4259_L
  split_ifs
  · exact p4259_Lup_min g z k hz (p4259_G_ge g k le_rfl)
  · unfold p4259_Ldown; exact (Nat.findGreatest_le z).trans hz.le

private lemma p4259_L_self {k : ℕ} (g : Fin k → Bool) (z : ℕ) (hz : p4259_G g z = false) :
    p4259_L g z ≤ z := by
  unfold p4259_L; rw [if_neg (by simp [hz])]; unfold p4259_Ldown; exact Nat.findGreatest_le z

open AllocationIndices in
private lemma p4259_L_thr {k : ℕ} (y : ℕ) (hy : y ≤ k) (z : ℕ) :
    p4259_L (plateThreshold (k := k) y) z = y := by
  have hG : ∀ j, p4259_G (plateThreshold (k := k) y) j = decide (j < y) := by
    intro j; unfold p4259_G plateThreshold
    split_ifs with h
    · rfl
    · have : ¬ j < y := by omega
      simp [this]
  unfold p4259_L
  rw [hG z]
  by_cases hzy : z < y
  · rw [if_pos (by simpa using hzy)]
    obtain ⟨s1, s2⟩ := p4259_Lup_spec (plateThreshold (k := k) y) z
    rw [hG] at s2
    have := p4259_Lup_min (plateThreshold (k := k) y) z y hzy (by rw [hG]; simp)
    simp at s2
    omega
  · rw [if_neg (by simpa using hzy)]
    unfold p4259_Ldown
    rw [Nat.findGreatest_eq_iff]
    refine ⟨by omega, fun hy0 ↦ ⟨by omega, ?_⟩, fun n hn1 hn2 ↦ ?_⟩
    · rw [hG]; simp only [decide_eq_true_eq]; omega
    · rw [hG]; simp only [decide_eq_true_eq, not_and, not_lt]; intro _; omega

/-! ### Evaluations of the model quantities -/

open AllocationIndices in
private lemma p4259_share_k {k : ℕ} (lam mu : Fin k → ℝ) (hk : 0 < k) :
    plateShare lam mu k = 0 := by
  unfold plateShare; rw [dif_neg (by omega), if_neg (by omega)]

open AllocationIndices in
private lemma p4259_share_0 {k : ℕ} (lam mu : Fin k → ℝ) : plateShare lam mu 0 = 1 := by
  unfold plateShare; rw [dif_neg (by omega), if_pos rfl]

open AllocationIndices in
private lemma p4259_share_mid {k : ℕ} (lam mu : Fin k → ℝ) (n : ℕ) (h0 : 0 < n) (hn : n < k) :
    plateShare lam mu n = lam ⟨n - 1, by omega⟩ / (lam ⟨n - 1, by omega⟩ + mu ⟨n, hn⟩) := by
  unfold plateShare; rw [dif_pos ⟨h0, hn⟩]

open AllocationIndices in
private lemma p4259_ext_lt {k : ℕ} (r : Fin k → ℝ) (n : ℕ) (hn : n < k) :
    extendReward r n = r ⟨n, hn⟩ := by
  unfold extendReward; rw [dif_pos hn]

open AllocationIndices in
private lemma p4259_ext_ge {k : ℕ} (r : Fin k → ℝ) (n : ℕ) (hn : k ≤ n) :
    extendReward r n = 0 := by
  unfold extendReward; rw [dif_neg (by omega)]

open AllocationIndices in
private lemma p4259_lam_pos {k : ℕ} (lam mu : Fin k → ℝ) (hlam : ∀ x, lam x ∈ Set.Icc (0 : ℝ) 1)
    (hphi : StrictAntiOn (plateShare lam mu) (Set.Iic k)) (n : ℕ) (hn : n + 1 < k) :
    0 < lam ⟨n, by omega⟩ := by
  have h := hphi (Set.mem_Iic.2 (show n + 1 ≤ k by omega)) (Set.mem_Iic.2 le_rfl) hn
  rw [p4259_share_k lam mu (by omega), p4259_share_mid lam mu (n + 1) (by omega) hn] at h
  rcases (hlam ⟨n, by omega⟩).1.lt_or_eq with h1 | h1
  · exact h1
  · exfalso
    have e : lam ⟨n + 1 - 1, by omega⟩ = lam ⟨n, by omega⟩ := rfl
    rw [e, ← h1] at h
    simp at h

open AllocationIndices in
private lemma p4259_mu_pos {k : ℕ} (lam mu : Fin k → ℝ) (hlam : ∀ x, lam x ∈ Set.Icc (0 : ℝ) 1)
    (hmu : ∀ x, mu x ∈ Set.Icc (0 : ℝ) 1)
    (hphi : StrictAntiOn (plateShare lam mu) (Set.Iic k)) (n : ℕ) (hn : n < k) (h0 : 0 < n) :
    0 < mu ⟨n, hn⟩ := by
  have h := hphi (Set.mem_Iic.2 (Nat.zero_le k)) (Set.mem_Iic.2 hn.le) h0
  rw [p4259_share_0, p4259_share_mid lam mu n h0 hn] at h
  have hl := p4259_lam_pos lam mu hlam hphi (n - 1) (by omega)
  have e : lam ⟨n - 1, by omega⟩ = lam ⟨n - 1 , by omega⟩ := rfl
  rcases (hmu ⟨n, hn⟩).1.lt_or_eq with h1 | h1
  · exact h1
  · exfalso
    rw [← h1, add_zero, div_self hl.ne'] at h
    exact lt_irrefl _ h

open AllocationIndices in
private lemma p4259_share_strict {k : ℕ} (lam mu : Fin k → ℝ)
    (hphi : StrictAntiOn (plateShare lam mu) (Set.Iic k)) (a b : ℕ) (hab : a < b) (hb : b ≤ k) :
    plateShare lam mu b < plateShare lam mu a :=
  hphi (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 hb) hab

open MeasureTheory ProbabilityTheory AllocationIndices in
private lemma p4259_drift_int {k : ℕ} (p : Fin k → ℝ) (F : Fin k → Fin k)
    (hp : ∀ x, p x ∈ Set.Icc (0 : ℝ) 1) (u : Fin k → ℝ) (x : Fin k) :
    ∫ y, u y ∂(driftKernel p F x) = p x * u (F x) + (1 - p x) * u x := by
  have e : driftKernel p F x =
      ENNReal.ofReal (p x) • Measure.dirac (F x) + ENNReal.ofReal (1 - p x) • Measure.dirac x := rfl
  rw [e, integral_add_measure (Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top)
      (Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal (hp x).1, ENNReal.toReal_ofReal (by linarith [(hp x).2])]
  simp [smul_eq_mul]

open MeasureTheory ProbabilityTheory AllocationIndices in
private lemma p4259_sk_int {k : ℕ} (lam mu r : Fin k → ℝ)
    (hlam : ∀ x, lam x ∈ Set.Icc (0 : ℝ) 1) (hmu : ∀ x, mu x ∈ Set.Icc (0 : ℝ) 1)
    (g : Fin k → Bool) (u : Fin k → ℝ) (z : Fin k) :
    ∫ y, u y ∂(stationaryKernel (spinningPlates lam mu r hlam hmu) g z) =
      if g z = true then lam z * u (upState z) + (1 - lam z) * u z
      else mu z * u (downState z) + (1 - mu z) * u z := by
  have e : stationaryKernel (spinningPlates lam mu r hlam hmu) g z =
      (if g z = true then driftKernel lam upState else driftKernel mu downState) z := rfl
  rw [e]
  cases g z
  · simp only [Bool.false_eq_true, if_false]; exact p4259_drift_int mu _ hmu u z
  · simp only [if_true]; exact p4259_drift_int lam _ hlam u z

/-! ### The Poisson equation of an arbitrary stationary policy -/

open AllocationIndices in
private noncomputable def p4259_V {k : ℕ} (lam mu r : Fin k → ℝ) (W : ℝ) (y : ℕ) : ℝ :=
  W * plateShare lam mu y + plateReturn lam mu r y

open AllocationIndices in
private noncomputable def p4259_f {k : ℕ} (r : Fin k → ℝ) (W : ℝ) (g : Fin k → Bool) (j : ℕ) : ℝ :=
  extendReward r j + if p4259_G g j = true then 0 else W

private noncomputable def p4259_c {k : ℕ} (lam mu r : Fin k → ℝ) (W : ℝ) (g : Fin k → Bool)
    (j : ℕ) : ℝ :=
  p4259_V lam mu r W (p4259_L g j)

open AllocationIndices in
private noncomputable def p4259_d {k : ℕ} (lam mu r : Fin k → ℝ) (W : ℝ) (g : Fin k → Bool)
    (j : ℕ) : ℝ :=
  if p4259_G g j = true then
    (p4259_f r W g j - p4259_c lam mu r W g j) / extendReward lam j
  else if p4259_G g (j + 1) = false then
    -((p4259_f r W g (j + 1) - p4259_c lam mu r W g (j + 1)) / extendReward mu (j + 1))
  else 0

private noncomputable def p4259_h {k : ℕ} (lam mu r : Fin k → ℝ) (W : ℝ) (g : Fin k → Bool)
    (z : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico z (k - 1), p4259_d lam mu r W g j

private lemma p4259_h_split {k : ℕ} (lam mu r : Fin k → ℝ) (W : ℝ) (g : Fin k → Bool)
    (z : ℕ) (hz : z + 1 < k) :
    p4259_h lam mu r W g z = p4259_d lam mu r W g z + p4259_h lam mu r W g (z + 1) := by
  unfold p4259_h
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]

open AllocationIndices in
private lemma p4259_V0 {k : ℕ} (lam mu r : Fin k → ℝ) (W : ℝ) :
    p4259_V lam mu r W 0 = W + extendReward r 0 := by
  unfold p4259_V plateReturn; rw [p4259_share_0]; ring

open AllocationIndices in
private lemma p4259_Vk {k : ℕ} (lam mu r : Fin k → ℝ) (W : ℝ) (hk : 0 < k) :
    p4259_V lam mu r W k = extendReward r (k - 1) := by
  unfold p4259_V plateReturn; rw [p4259_share_k lam mu hk, p4259_ext_ge r k le_rfl]; ring

open AllocationIndices in
private lemma p4259_f_T {k : ℕ} (r : Fin k → ℝ) (W : ℝ) (g : Fin k → Bool) (j : ℕ)
    (hj : p4259_G g j = true) : p4259_f r W g j = extendReward r j := by
  unfold p4259_f; rw [if_pos hj]; ring

open AllocationIndices in
private lemma p4259_f_F {k : ℕ} (r : Fin k → ℝ) (W : ℝ) (g : Fin k → Bool) (j : ℕ)
    (hj : p4259_G g j = false) : p4259_f r W g j = extendReward r j + W := by
  unfold p4259_f; rw [if_neg (by simp [hj])]

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset Filter AllocationIndices in
private lemma p4259_avg_eq {k : ℕ} (lam mu r : Fin k → ℝ)
    (hlam : ∀ x, lam x ∈ Set.Icc (0 : ℝ) 1) (hmu : ∀ x, mu x ∈ Set.Icc (0 : ℝ) 1)
    (hlam_top : ∀ x : Fin k, x.val + 1 = k → lam x = 0)
    (hmu_bot : ∀ x : Fin k, x.val = 0 → mu x = 0)
    (hphi : StrictAntiOn (plateShare lam mu) (Set.Iic k))
    (W : ℝ) (g : Fin k → Bool) (x : Fin k) :
    avgReward (spinningPlates lam mu r hlam hmu) W g x = p4259_V lam mu r W (p4259_L g x.val) := by
  unfold avgReward stationaryExpectedReward
  refine p4259_avg (stationaryKernel (spinningPlates lam mu r hlam hmu) g)
    (subsidizedReward (spinningPlates lam mu r hlam hmu) W g)
    (fun z ↦ p4259_c lam mu r W g z.val) (fun z ↦ p4259_h lam mu r W g z.val) ?_ ?_ x
  · intro z
    rw [p4259_sk_int]
    have hn := z.isLt
    cases hgz : g z
    · simp only [Bool.false_eq_true, if_false]
      rcases Nat.eq_zero_or_pos z.val with h0 | h0
      · rw [hmu_bot z h0]; ring
      · have hd : downState z = ⟨z.val - 1, by omega⟩ :=
          Fin.ext (by simp [downState])
        rw [hd]
        have := p4259_L_dn g z.val (by rw [p4259_G_fin, hgz]) h0
        simp only [p4259_c]
        rw [this]; ring
    · simp only [if_true]
      by_cases hk : z.val + 1 < k
      · have hu : upState z = ⟨z.val + 1, hk⟩ :=
          Fin.ext (by simp [upState]; omega)
        rw [hu]
        have := p4259_L_up g z.val (by rw [p4259_G_fin, hgz]) hk
        simp only [p4259_c]
        rw [this]; ring
      · rw [hlam_top z (by omega)]; ring
  · intro z
    rw [p4259_sk_int]
    have hn := z.isLt
    have hf : subsidizedReward (spinningPlates lam mu r hlam hmu) W g z = p4259_f r W g z.val := by
      unfold subsidizedReward p4259_f extendReward
      rw [p4259_G_fin, dif_pos z.isLt]; rfl
    rw [hf]
    have hG := p4259_G_fin g z
    cases hgz : g z
    · rw [hgz] at hG
      simp only [Bool.false_eq_true, if_false]
      rcases Nat.eq_zero_or_pos z.val with h0 | h0
      · rw [hmu_bot z h0]
        have hG0 : p4259_G g 0 = false := by rw [← h0]; exact hG
        simp only [p4259_c]
        rw [h0, p4259_L_zero g hG0, p4259_V0, p4259_f_F r W g 0 hG0]
        ring
      · have hd : downState z = ⟨z.val - 1, by omega⟩ :=
          Fin.ext (by simp [downState])
        rw [hd]
        have hmz := p4259_mu_pos lam mu hlam hmu hphi z.val hn h0
        have hsp := p4259_h_split lam mu r W g (z.val - 1) (by omega)
        have e1 : z.val - 1 + 1 = z.val := by omega
        rw [e1] at hsp
        simp only
        rw [hsp]
        have hmz' : mu ⟨z.val, hn⟩ = mu z := rfl
        rw [hmz'] at hmz
        cases h1 : p4259_G g (z.val - 1) with
        | true =>
          -- the pair class {z - 1, z}
          have hdd : p4259_d lam mu r W g (z.val - 1) =
              (p4259_f r W g (z.val - 1) - p4259_c lam mu r W g (z.val - 1)) /
                extendReward lam (z.val - 1) := by
            unfold p4259_d; rw [if_pos h1]
          rw [hdd]
          have hLz : p4259_L g z.val = z.val := by
            have := p4259_L_pair g (z.val - 1) h1 (by rw [e1]; exact hG)
            rwa [e1] at this
          have hc1 : p4259_c lam mu r W g (z.val - 1) = p4259_c lam mu r W g z.val := by
            unfold p4259_c; rw [p4259_L_dn g z.val hG h0]
          rw [hc1, p4259_f_T r W g _ h1, p4259_f_F r W g _ hG]
          unfold p4259_c; rw [hLz]
          unfold p4259_V plateReturn
          rw [p4259_share_mid lam mu z.val h0 hn, p4259_ext_lt lam (z.val - 1) (by omega),
            p4259_ext_lt r (z.val - 1) (by omega), p4259_ext_lt r z.val hn]
          have hl := p4259_lam_pos lam mu hlam hphi (z.val - 1) (by omega)
          have hmz'' : mu ⟨z.val, hn⟩ = mu z := rfl
          rw [hmz'']
          set l := lam ⟨z.val - 1, by omega⟩ with hl_def
          set m := mu z with hm_def
          set a := r ⟨z.val - 1, by omega⟩
          set b := r ⟨z.val, hn⟩
          have hlm : 0 < l + m := by linarith
          field_simp
          ring
        | false =>
          have hdd : p4259_d lam mu r W g (z.val - 1) =
              -((p4259_f r W g z.val - p4259_c lam mu r W g z.val) / extendReward mu z.val) := by
            unfold p4259_d; rw [if_neg (by simp [h1]), e1, if_pos hG]
          rw [hdd, p4259_ext_lt mu z.val hn]
          have hmz'' : mu ⟨z.val, hn⟩ = mu z := rfl
          rw [hmz'']
          field_simp
          ring
    · rw [hgz] at hG
      simp only [if_true]
      by_cases hk : z.val + 1 < k
      · have hu : upState z = ⟨z.val + 1, hk⟩ :=
          Fin.ext (by simp [upState]; omega)
        rw [hu]
        have hlz := p4259_lam_pos lam mu hlam hphi z.val hk
        have hlz' : lam ⟨z.val, by omega⟩ = lam z := rfl
        rw [hlz'] at hlz
        have hsp := p4259_h_split lam mu r W g z.val hk
        simp only
        rw [hsp]
        have hdd : p4259_d lam mu r W g z.val =
            (p4259_f r W g z.val - p4259_c lam mu r W g z.val) / extendReward lam z.val := by
          unfold p4259_d; rw [if_pos hG]
        rw [hdd, p4259_ext_lt lam z.val hn]
        have hlz'' : lam ⟨z.val, hn⟩ = lam z := rfl
        rw [hlz'']
        field_simp
        ring
      · rw [hlam_top z (by omega)]
        simp only [p4259_c]
        rw [p4259_L_top g z.val hG (by omega), p4259_Vk lam mu r W (by omega),
          p4259_f_T r W g _ hG]
        have e2 : k - 1 = z.val := by omega
        rw [e2]
        ring

/-! ### The optimal average reward, optimal policies and the passive set -/

open AllocationIndices in
private lemma p4259_V_le {k : ℕ} (lam mu r : Fin k → ℝ) (W : ℝ) (y : ℕ) (hy : y ≤ k) :
    p4259_V lam mu r W y ≤ plateEnvelope lam mu r W := by
  unfold plateEnvelope p4259_V
  exact Finset.le_sup' (fun y ↦ W * plateShare lam mu y + plateReturn lam mu r y)
    (Finset.mem_range.2 (by omega))

open AllocationIndices in
private lemma p4259_V_ex {k : ℕ} (lam mu r : Fin k → ℝ) (W : ℝ) :
    ∃ y, y ≤ k ∧ p4259_V lam mu r W y = plateEnvelope lam mu r W := by
  obtain ⟨y, hy, hyM⟩ := Finset.exists_mem_eq_sup' (s := Finset.range (k + 1)) (by simp)
    (fun y ↦ W * plateShare lam mu y + plateReturn lam mu r y)
  refine ⟨y, by simp at hy; omega, ?_⟩
  unfold plateEnvelope p4259_V
  exact hyM.symm

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices in
private lemma p4259_opt {k : ℕ} (lam mu r : Fin k → ℝ)
    (hlam : ∀ x, lam x ∈ Set.Icc (0 : ℝ) 1) (hmu : ∀ x, mu x ∈ Set.Icc (0 : ℝ) 1)
    (hlam_top : ∀ x : Fin k, x.val + 1 = k → lam x = 0)
    (hmu_bot : ∀ x : Fin k, x.val = 0 → mu x = 0)
    (hphi : StrictAntiOn (plateShare lam mu) (Set.Iic k)) (hk : 0 < k) (W : ℝ) :
    optimalAvg (spinningPlates lam mu r hlam hmu) W = plateEnvelope lam mu r W := by
  have hne : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  unfold optimalAvg
  apply le_antisymm
  · refine ciSup_le fun g ↦ ciSup_le fun x ↦ ?_
    rw [p4259_avg_eq lam mu r hlam hmu hlam_top hmu_bot hphi]
    exact p4259_V_le lam mu r W _ (p4259_L_le g x.val x.isLt)
  · obtain ⟨y, hyk, hyM⟩ := p4259_V_ex lam mu r W
    rw [← hyM]
    have h1 : p4259_V lam mu r W y =
        avgReward (spinningPlates lam mu r hlam hmu) W (plateThreshold (k := k) y) ⟨0, hk⟩ := by
      rw [p4259_avg_eq lam mu r hlam hmu hlam_top hmu_bot hphi, p4259_L_thr y hyk]
    rw [h1]
    refine le_ciSup_of_le (Set.finite_range _).bddAbove (plateThreshold (k := k) y) ?_
    exact le_ciSup_of_le (Set.finite_range _).bddAbove ⟨0, hk⟩ le_rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices in
private lemma p4259_passive {k : ℕ} (lam mu r : Fin k → ℝ)
    (hlam : ∀ x, lam x ∈ Set.Icc (0 : ℝ) 1) (hmu : ∀ x, mu x ∈ Set.Icc (0 : ℝ) 1)
    (hlam_top : ∀ x : Fin k, x.val + 1 = k → lam x = 0)
    (hmu_bot : ∀ x : Fin k, x.val = 0 → mu x = 0)
    (hphi : StrictAntiOn (plateShare lam mu) (Set.Iic k)) (hk : 0 < k) (W : ℝ) (x : Fin k) :
    x ∈ passiveSet (spinningPlates lam mu r hlam hmu) W ↔
      ∃ y, y ≤ x.val ∧ p4259_V lam mu r W y = plateEnvelope lam mu r W := by
  unfold passiveSet IsAvgOptimal
  simp only [Set.mem_ofPred_eq, p4259_avg_eq lam mu r hlam hmu hlam_top hmu_bot hphi,
    p4259_opt lam mu r hlam hmu hlam_top hmu_bot hphi hk]
  constructor
  · rintro ⟨g, hg, hgx⟩
    exact ⟨p4259_L g x.val, p4259_L_self g x.val (by rw [p4259_G_fin, hgx]), hg x⟩
  · rintro ⟨y, hy, hV⟩
    refine ⟨plateThreshold (k := k) y, fun z ↦ ?_, ?_⟩
    · rw [p4259_L_thr y (by omega)]; exact hV
    · unfold plateThreshold; simp only [decide_eq_false_iff_not, not_lt]; exact hy

open AllocationIndices in
private lemma p4259_cmp {k : ℕ} (lam mu r : Fin k → ℝ)
    (hphi : StrictAntiOn (plateShare lam mu) (Set.Iic k)) (W : ℝ) (y : Fin k) :
    p4259_V lam mu r W (y.val + 1) ≤ p4259_V lam mu r W y.val ↔ plateIndex lam mu r y ≤ W := by
  have hd := p4259_share_strict lam mu hphi y.val (y.val + 1) (by omega) (by have := y.isLt; omega)
  have hpos : 0 < plateShare lam mu y.val - plateShare lam mu (y.val + 1) := by linarith
  unfold plateIndex p4259_V
  rw [div_le_iff₀ hpos]
  constructor <;> intro h <;> nlinarith

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices in
theorem solution {k : ℕ} (lam mu r : Fin k → ℝ)
    (hlam : ∀ x, lam x ∈ Set.Icc (0 : ℝ) 1) (hmu : ∀ x, mu x ∈ Set.Icc (0 : ℝ) 1)
    (hlam_top : ∀ x : Fin k, x.val + 1 = k → lam x = 0)
    (hmu_bot : ∀ x : Fin k, x.val = 0 → mu x = 0)
    (hr : Monotone r) (hr0 : ∀ x, 0 ≤ r x)
    (hphi : StrictAntiOn (plateShare lam mu) (Set.Iic k)) :
    Indexable (spinningPlates lam mu r hlam hmu) ∧
    (StrictAnti (plateIndex lam mu r) →
      ∀ x, whittleIndex (spinningPlates lam mu r hlam hmu) x = plateIndex lam mu r x) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    exact ⟨fun _ _ _ x ↦ x.elim0, fun _ x ↦ x.elim0⟩
  have hP := p4259_passive lam mu r hlam hmu hlam_top hmu_bot hphi hk
  refine ⟨fun W W' hWW' x hx ↦ ?_, fun hanti x ↦ ?_⟩
  · -- indexability
    rw [hP] at hx ⊢
    obtain ⟨y, hyx, hyV⟩ := hx
    obtain ⟨y', hy'k, hy'V⟩ := p4259_V_ex lam mu r W'
    by_cases hyy : y' ≤ x.val
    · exact ⟨y', hyy, hy'V⟩
    · refine ⟨y, hyx, le_antisymm (p4259_V_le lam mu r W' y (by omega)) ?_⟩
      rw [← hy'V]
      have hs := p4259_share_strict lam mu hphi y y' (by omega) hy'k
      have h1 := p4259_V_le lam mu r W y' hy'k
      rw [← hyV] at h1
      unfold p4259_V at h1 ⊢
      nlinarith
  · -- the Whittle index
    have hset : {W : ℝ | x ∈ passiveSet (spinningPlates lam mu r hlam hmu) W} =
        Set.Ici (plateIndex lam mu r x) := by
      ext W
      simp only [Set.mem_ofPred_eq, Set.mem_Ici, hP]
      constructor
      · rintro ⟨y, hyx, hyV⟩
        have hyk : y < k := by have := x.isLt; omega
        have h1 : p4259_V lam mu r W ((⟨y, hyk⟩ : Fin k).val + 1) ≤
            p4259_V lam mu r W (⟨y, hyk⟩ : Fin k).val := by
          simp only
          rw [hyV]; exact p4259_V_le lam mu r W _ (by omega)
        rw [p4259_cmp lam mu r hphi W ⟨y, hyk⟩] at h1
        exact le_trans (hanti.antitone (show (⟨y, hyk⟩ : Fin k) ≤ x from hyx)) h1
      · intro hW
        -- beyond `x` the thresholds only lose
        have hdesc : ∀ j, x.val ≤ j → j ≤ k → p4259_V lam mu r W j ≤ p4259_V lam mu r W x.val := by
          intro j hj
          induction j, hj using Nat.le_induction with
          | base => intro _; exact le_rfl
          | succ j hxj ih =>
            intro hjk
            have hjk' : j < k := by omega
            have h2 : plateIndex lam mu r ⟨j, hjk'⟩ ≤ W :=
              le_trans (hanti.antitone (show x ≤ (⟨j, hjk'⟩ : Fin k) from hxj)) hW
            rw [← p4259_cmp lam mu r hphi W ⟨j, hjk'⟩] at h2
            exact le_trans h2 (ih (by omega))
        obtain ⟨y, hy, hyM⟩ := Finset.exists_mem_eq_sup' (s := Finset.range (x.val + 1)) (by simp)
          (fun y ↦ p4259_V lam mu r W y)
        have hyx : y ≤ x.val := by simp at hy; omega
        have hle : ∀ j, j ≤ x.val → p4259_V lam mu r W j ≤ p4259_V lam mu r W y := by
          intro j hj
          rw [← hyM]
          exact Finset.le_sup' (fun y ↦ p4259_V lam mu r W y) (Finset.mem_range.2 (by omega))
        refine ⟨y, hyx, le_antisymm (p4259_V_le lam mu r W y (by have := x.isLt; omega)) ?_⟩
        unfold plateEnvelope
        refine Finset.sup'_le _ _ fun j hj ↦ ?_
        have hjk : j ≤ k := by simp at hj; omega
        show p4259_V lam mu r W j ≤ p4259_V lam mu r W y
        by_cases hjx : j ≤ x.val
        · exact hle j hjx
        · exact le_trans (hdesc j (by omega) hjk) (hle x.val le_rfl)
    unfold whittleIndex
    rw [hset, csInf_Ici]
