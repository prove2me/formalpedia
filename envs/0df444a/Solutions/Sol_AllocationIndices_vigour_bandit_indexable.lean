-- Prove2me | solution 1 for AllocationIndices.vigour_bandit_indexable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T14:12:14.744379+00:00
-- url     : https://prove2.me/submissions/3f043ad7-371d-4fe0-9f21-aec025660351

import Mathlib
import Definitions.Def_AllocationIndices_Restless

set_option autoImplicit false

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p94ef_prob {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : IsProbabilityMeasure (markovChainMeasure P x) := by
  unfold markovChainMeasure; infer_instance

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p94ef_marg0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : (markovChainMeasure P x).map (Preorder.frestrictLe 0) =
      Measure.dirac (fun _ ↦ x) := by
  rw [markovChainMeasure, Kernel.trajMeasure,
    Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_dirac' (MeasurableEquiv.measurable _)]
  congr 1

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p94ef_int0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) (F : S → ℝ) (hF : Measurable F) :
    ∫ ω, F (ω 0) ∂markovChainMeasure P x = F x := by
  have hFm : Measurable (fun h : (Π _i : Finset.Iic 0, S) ↦ F (h ⟨0, Finset.mem_Iic.2 le_rfl⟩)) :=
    hF.comp (measurable_pi_apply _)
  have h1 := integral_map (μ := markovChainMeasure P x) (Preorder.measurable_frestrictLe 0).aemeasurable
    hFm.aestronglyMeasurable
  rw [p94ef_marg0, integral_dirac' _ _ hFm.stronglyMeasurable] at h1
  exact h1.symm

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p94ef_int_of_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (F : α → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ x, |F x| ≤ B) :
    Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p94ef_step {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) (s : ℕ) (g : S → ℝ) (Bg : ℝ)
    (hg : ∀ y, |g y| ≤ Bg) :
    ∫ ω, g (ω (s + 1)) ∂markovChainMeasure P x =
      ∫ ω, (∫ z, g z ∂P (ω s)) ∂markovChainMeasure P x := by
  have := p94ef_prob P x
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
    p94ef_int_of_bound _ _ hFm Bg (fun p ↦ hg _)
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
private lemma p94ef_avg {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Fintype S]
    (P : Kernel S S) [IsMarkovKernel P] (f c h : S → ℝ)
    (hc : ∀ z, ∫ y, c y ∂P z = c z) (hh : ∀ z, f z + ∫ y, h y ∂P z = c z + h z) (x : S) :
    limsup (fun T : ℕ ↦ (T : ℝ)⁻¹ * ∑ t ∈ range T, ∫ ω, f (ω t) ∂markovChainMeasure P x)
      atTop = c x := by
  have := p94ef_prob P x
  have hbd : ∀ u : S → ℝ, ∀ y, |u y| ≤ ∑ z, |u z| := fun u y ↦
    Finset.single_le_sum (f := fun z ↦ |u z|) (fun z _ ↦ abs_nonneg _) (Finset.mem_univ y)
  have hint : ∀ (u : S → ℝ) (t : ℕ),
      Integrable (fun ω : ℕ → S ↦ u (ω t)) (markovChainMeasure P x) := fun u t ↦
    p94ef_int_of_bound _ _ ((Measurable.of_discrete (f := u)).comp (measurable_pi_apply t)) _
      (fun ω ↦ hbd u (ω t))
  have hstep : ∀ (u : S → ℝ) (t : ℕ), ∫ ω, u (ω (t + 1)) ∂markovChainMeasure P x =
      ∫ ω, (∫ y, u y ∂P (ω t)) ∂markovChainMeasure P x := fun u t ↦
    p94ef_step P x t u _ (hbd u)
  have hc' : ∀ t, ∫ ω, c (ω t) ∂markovChainMeasure P x = c x := by
    intro t
    induction t with
    | zero => exact p94ef_int0 P x c Measurable.of_discrete
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
    | zero => simp [p94ef_int0 P x h Measurable.of_discrete]
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

private def p94ef_G {k : ℕ} (g : Fin k → Bool) (j : ℕ) : Bool :=
  if h : j < k then g ⟨j, h⟩ else false

private lemma p94ef_G_ge {k : ℕ} (g : Fin k → Bool) (j : ℕ) (hj : k ≤ j) :
    p94ef_G g j = false := by
  unfold p94ef_G; rw [dif_neg (by omega)]

private lemma p94ef_G_fin {k : ℕ} (g : Fin k → Bool) (z : Fin k) : p94ef_G g z.val = g z := by
  unfold p94ef_G; rw [dif_pos z.isLt]

private lemma p94ef_ex {k : ℕ} (g : Fin k → Bool) (z : ℕ) :
    ∃ j, z < j ∧ p94ef_G g j = false :=
  ⟨z + k + 1, by omega, p94ef_G_ge g _ (by omega)⟩

private noncomputable def p94ef_Lup {k : ℕ} (g : Fin k → Bool) (z : ℕ) : ℕ :=
  Nat.find (p94ef_ex g z)

private lemma p94ef_Lup_spec {k : ℕ} (g : Fin k → Bool) (z : ℕ) :
    z < p94ef_Lup g z ∧ p94ef_G g (p94ef_Lup g z) = false :=
  Nat.find_spec (p94ef_ex g z)

private lemma p94ef_Lup_min {k : ℕ} (g : Fin k → Bool) (z j : ℕ) (hj : z < j)
    (hg : p94ef_G g j = false) : p94ef_Lup g z ≤ j :=
  Nat.find_min' (p94ef_ex g z) ⟨hj, hg⟩

private def p94ef_Ldown {k : ℕ} (g : Fin k → Bool) (z : ℕ) : ℕ :=
  Nat.findGreatest (fun y ↦ 0 < y ∧ p94ef_G g (y - 1) = true) z

private noncomputable def p94ef_L {k : ℕ} (g : Fin k → Bool) (z : ℕ) : ℕ :=
  if p94ef_G g z = true then p94ef_Lup g z else p94ef_Ldown g z

private lemma p94ef_L_up {k : ℕ} (g : Fin k → Bool) (z : ℕ) (hz : p94ef_G g z = true)
    (_hk : z + 1 < k) : p94ef_L g (z + 1) = p94ef_L g z := by
  have hLz : p94ef_L g z = p94ef_Lup g z := by unfold p94ef_L; rw [if_pos hz]
  rw [hLz]
  obtain ⟨s1, s2⟩ := p94ef_Lup_spec g z
  cases h1 : p94ef_G g (z + 1) with
  | false =>
    have e1 : p94ef_L g (z + 1) = z + 1 := by
      unfold p94ef_L; rw [if_neg (by simp [h1])]
      unfold p94ef_Ldown
      exact Nat.findGreatest_eq ⟨by omega, by simpa using hz⟩
    have := p94ef_Lup_min g z (z + 1) (by omega) h1
    omega
  | true =>
    have e1 : p94ef_L g (z + 1) = p94ef_Lup g (z + 1) := by unfold p94ef_L; rw [if_pos h1]
    rw [e1]
    obtain ⟨t1, t2⟩ := p94ef_Lup_spec g (z + 1)
    have a1 := p94ef_Lup_min g z _ (by omega) t2
    have hne : p94ef_Lup g z ≠ z + 1 := by
      intro he; rw [he, h1] at s2; exact absurd s2 (by decide)
    have a2 := p94ef_Lup_min g (z + 1) _ (by omega) s2
    omega

private lemma p94ef_L_pair {k : ℕ} (g : Fin k → Bool) (m : ℕ) (hm : p94ef_G g m = true)
    (hm1 : p94ef_G g (m + 1) = false) : p94ef_L g (m + 1) = m + 1 := by
  unfold p94ef_L; rw [if_neg (by simp [hm1])]
  unfold p94ef_Ldown
  exact Nat.findGreatest_eq ⟨by omega, by simpa using hm⟩

private lemma p94ef_L_dn {k : ℕ} (g : Fin k → Bool) (z : ℕ) (hz : p94ef_G g z = false)
    (h0 : 0 < z) : p94ef_L g (z - 1) = p94ef_L g z := by
  obtain ⟨m, rfl⟩ : ∃ m, z = m + 1 := ⟨z - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  cases h1 : p94ef_G g m with
  | true =>
    rw [p94ef_L_pair g m h1 hz]
    have e1 : p94ef_L g m = p94ef_Lup g m := by unfold p94ef_L; rw [if_pos h1]
    rw [e1]
    obtain ⟨s1, s2⟩ := p94ef_Lup_spec g m
    have := p94ef_Lup_min g m (m + 1) (by omega) hz
    omega
  | false =>
    have e1 : p94ef_L g m = p94ef_Ldown g m := by unfold p94ef_L; rw [if_neg (by simp [h1])]
    have e2 : p94ef_L g (m + 1) = p94ef_Ldown g (m + 1) := by
      unfold p94ef_L; rw [if_neg (by simp [hz])]
    rw [e1, e2]
    unfold p94ef_Ldown
    rw [Nat.findGreatest_of_not]
    simp [h1]

private lemma p94ef_L_top {k : ℕ} (g : Fin k → Bool) (z : ℕ) (hz : p94ef_G g z = true)
    (hk : z + 1 = k) : p94ef_L g z = k := by
  unfold p94ef_L; rw [if_pos hz]
  obtain ⟨s1, s2⟩ := p94ef_Lup_spec g z
  have := p94ef_Lup_min g z k (by omega) (p94ef_G_ge g k le_rfl)
  omega

private lemma p94ef_L_zero {k : ℕ} (g : Fin k → Bool) (hz : p94ef_G g 0 = false) :
    p94ef_L g 0 = 0 := by
  unfold p94ef_L; rw [if_neg (by simp [hz])]; unfold p94ef_Ldown; exact Nat.findGreatest_zero

private lemma p94ef_L_le {k : ℕ} (g : Fin k → Bool) (z : ℕ) (hz : z < k) : p94ef_L g z ≤ k := by
  unfold p94ef_L
  split_ifs
  · exact p94ef_Lup_min g z k hz (p94ef_G_ge g k le_rfl)
  · unfold p94ef_Ldown; exact (Nat.findGreatest_le z).trans hz.le

private lemma p94ef_L_self {k : ℕ} (g : Fin k → Bool) (z : ℕ) (hz : p94ef_G g z = false) :
    p94ef_L g z ≤ z := by
  unfold p94ef_L; rw [if_neg (by simp [hz])]; unfold p94ef_Ldown; exact Nat.findGreatest_le z

open AllocationIndices in
private lemma p94ef_L_thr {k : ℕ} (y : ℕ) (hy : y ≤ k) (z : ℕ) :
    p94ef_L (plateThreshold (k := k) y) z = y := by
  have hG : ∀ j, p94ef_G (plateThreshold (k := k) y) j = decide (j < y) := by
    intro j; unfold p94ef_G plateThreshold
    split_ifs with h
    · rfl
    · have : ¬ j < y := by omega
      simp [this]
  unfold p94ef_L
  rw [hG z]
  by_cases hzy : z < y
  · rw [if_pos (by simpa using hzy)]
    obtain ⟨s1, s2⟩ := p94ef_Lup_spec (plateThreshold (k := k) y) z
    rw [hG] at s2
    have := p94ef_Lup_min (plateThreshold (k := k) y) z y hzy (by rw [hG]; simp)
    simp at s2
    omega
  · rw [if_neg (by simpa using hzy)]
    unfold p94ef_Ldown
    rw [Nat.findGreatest_eq_iff]
    refine ⟨by omega, fun hy0 ↦ ⟨by omega, ?_⟩, fun n hn1 hn2 ↦ ?_⟩
    · rw [hG]; simp only [decide_eq_true_eq]; omega
    · rw [hG]; simp only [decide_eq_true_eq, not_and, not_lt]; intro _; omega


/-! ### The vigour model: evaluations -/

open AllocationIndices in
private lemma p94ef_share_k {k : ℕ} (nu rho : Fin k → ℝ) (hk : 0 < k) :
    vigourShare nu rho k = 1 := by
  unfold vigourShare; rw [dif_neg (by omega), if_neg (by omega)]

open AllocationIndices in
private lemma p94ef_share_0 {k : ℕ} (nu rho : Fin k → ℝ) : vigourShare nu rho 0 = 0 := by
  unfold vigourShare; rw [dif_neg (by omega), if_pos rfl]

open AllocationIndices in
private lemma p94ef_share_mid {k : ℕ} (nu rho : Fin k → ℝ) (n : ℕ) (h0 : 0 < n) (hn : n < k) :
    vigourShare nu rho n = nu ⟨n, hn⟩ / (nu ⟨n, hn⟩ + rho ⟨n - 1, by omega⟩) := by
  unfold vigourShare; rw [dif_pos ⟨h0, hn⟩]

open AllocationIndices in
private lemma p94ef_ext_lt {k : ℕ} (r : Fin k → ℝ) (n : ℕ) (hn : n < k) :
    extendReward r n = r ⟨n, hn⟩ := by
  unfold extendReward; rw [dif_pos hn]

open AllocationIndices in
private lemma p94ef_ext_ge {k : ℕ} (r : Fin k → ℝ) (n : ℕ) (hn : k ≤ n) :
    extendReward r n = 0 := by
  unfold extendReward; rw [dif_neg (by omega)]

open AllocationIndices in
private lemma p94ef_nu_pos {k : ℕ} (nu rho : Fin k → ℝ) (hnu : ∀ x, nu x ∈ Set.Icc (0 : ℝ) 1)
    (hpsi : StrictMonoOn (vigourShare nu rho) (Set.Iic k)) (n : ℕ) (h0 : 0 < n) (hn : n < k) :
    0 < nu ⟨n, hn⟩ := by
  have h := hpsi (Set.mem_Iic.2 (Nat.zero_le k)) (Set.mem_Iic.2 hn.le) h0
  rw [p94ef_share_0, p94ef_share_mid nu rho n h0 hn] at h
  rcases (hnu ⟨n, hn⟩).1.lt_or_eq with h1 | h1
  · exact h1
  · exfalso
    rw [← h1, zero_div] at h
    exact lt_irrefl _ h

open AllocationIndices in
private lemma p94ef_rho_pos {k : ℕ} (nu rho : Fin k → ℝ) (hnu : ∀ x, nu x ∈ Set.Icc (0 : ℝ) 1)
    (hrho : ∀ x, rho x ∈ Set.Icc (0 : ℝ) 1)
    (hpsi : StrictMonoOn (vigourShare nu rho) (Set.Iic k)) (n : ℕ) (hn : n + 1 < k) :
    0 < rho ⟨n, by omega⟩ := by
  have h := hpsi (Set.mem_Iic.2 (show n + 1 ≤ k by omega)) (Set.mem_Iic.2 le_rfl) hn
  rw [p94ef_share_k nu rho (by omega), p94ef_share_mid nu rho (n + 1) (by omega) hn] at h
  have hv := p94ef_nu_pos nu rho hnu hpsi (n + 1) (by omega) hn
  rcases (hrho ⟨n, by omega⟩).1.lt_or_eq with h1 | h1
  · exact h1
  · exfalso
    have e : rho ⟨n + 1 - 1, by omega⟩ = rho ⟨n, by omega⟩ := rfl
    rw [e, ← h1, add_zero, div_self hv.ne'] at h
    exact lt_irrefl _ h

open AllocationIndices in
private lemma p94ef_share_strict {k : ℕ} (nu rho : Fin k → ℝ)
    (hpsi : StrictMonoOn (vigourShare nu rho) (Set.Iic k)) (a b : ℕ) (hab : a < b) (hb : b ≤ k) :
    vigourShare nu rho a < vigourShare nu rho b :=
  hpsi (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 hb) hab

open MeasureTheory ProbabilityTheory AllocationIndices in
private lemma p94ef_drift_int {k : ℕ} (p : Fin k → ℝ) (F : Fin k → Fin k)
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
private lemma p94ef_sk_int {k : ℕ} (nu rho r : Fin k → ℝ)
    (hnu : ∀ x, nu x ∈ Set.Icc (0 : ℝ) 1) (hrho : ∀ x, rho x ∈ Set.Icc (0 : ℝ) 1)
    (g : Fin k → Bool) (u : Fin k → ℝ) (z : Fin k) :
    ∫ y, u y ∂(stationaryKernel (vigourBandit nu rho r hnu hrho) g z) =
      if g z = true then nu z * u (downState z) + (1 - nu z) * u z
      else rho z * u (upState z) + (1 - rho z) * u z := by
  have e : stationaryKernel (vigourBandit nu rho r hnu hrho) g z =
      (if g z = true then driftKernel nu downState else driftKernel rho upState) z := rfl
  rw [e]
  cases g z
  · simp only [Bool.false_eq_true, if_false]; exact p94ef_drift_int rho _ hrho u z
  · simp only [if_true]; exact p94ef_drift_int nu _ hnu u z

/-! ### Reflection: the "moves up" indicator of a vigour policy -/

private def p94ef_a {k : ℕ} (g : Fin k → Bool) : Fin k → Bool := fun x ↦ !g x

private lemma p94ef_Ga {k : ℕ} (g : Fin k → Bool) (z : Fin k) :
    p94ef_G (p94ef_a g) z.val = !g z := p94ef_G_fin _ z

open AllocationIndices in
private lemma p94ef_a_thr {k : ℕ} (y : ℕ) :
    p94ef_a (vigourThreshold (k := k) y) = plateThreshold (k := k) y := by
  funext x
  simp only [p94ef_a, vigourThreshold, plateThreshold]
  by_cases h : y ≤ x.val
  · simp [h, Nat.not_lt.2 h]
  · simp [h, Nat.lt_of_not_le h]

/-! ### The Poisson equation of an arbitrary stationary policy -/

open AllocationIndices in
private noncomputable def p94ef_f {k : ℕ} (r : Fin k → ℝ) (W : ℝ) (g : Fin k → Bool) (j : ℕ) : ℝ :=
  if p94ef_G (p94ef_a g) j = true then W else extendReward r j

open AllocationIndices in
private noncomputable def p94ef_c {k : ℕ} (nu rho r : Fin k → ℝ) (W : ℝ) (g : Fin k → Bool)
    (j : ℕ) : ℝ :=
  vigourValue nu rho r W (p94ef_L (p94ef_a g) j)

open AllocationIndices in
private noncomputable def p94ef_d {k : ℕ} (nu rho r : Fin k → ℝ) (W : ℝ) (g : Fin k → Bool)
    (j : ℕ) : ℝ :=
  if p94ef_G (p94ef_a g) j = true then
    (p94ef_f r W g j - p94ef_c nu rho r W g j) / extendReward rho j
  else if p94ef_G (p94ef_a g) (j + 1) = false then
    -((p94ef_f r W g (j + 1) - p94ef_c nu rho r W g (j + 1)) / extendReward nu (j + 1))
  else 0

private noncomputable def p94ef_h {k : ℕ} (nu rho r : Fin k → ℝ) (W : ℝ) (g : Fin k → Bool)
    (z : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico z (k - 1), p94ef_d nu rho r W g j

private lemma p94ef_h_split {k : ℕ} (nu rho r : Fin k → ℝ) (W : ℝ) (g : Fin k → Bool)
    (z : ℕ) (hz : z + 1 < k) :
    p94ef_h nu rho r W g z = p94ef_d nu rho r W g z + p94ef_h nu rho r W g (z + 1) := by
  unfold p94ef_h
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]

open AllocationIndices in
private lemma p94ef_V0 {k : ℕ} (nu rho r : Fin k → ℝ) (W : ℝ) :
    vigourValue nu rho r W 0 = extendReward r 0 := by
  unfold vigourValue; rw [p94ef_share_0]; ring

open AllocationIndices in
private lemma p94ef_Vk {k : ℕ} (nu rho r : Fin k → ℝ) (W : ℝ) (hk : 0 < k) :
    vigourValue nu rho r W k = W := by
  unfold vigourValue; rw [p94ef_share_k nu rho hk, p94ef_ext_ge r k le_rfl]; ring

private lemma p94ef_f_T {k : ℕ} (r : Fin k → ℝ) (W : ℝ) (g : Fin k → Bool) (j : ℕ)
    (hj : p94ef_G (p94ef_a g) j = true) : p94ef_f r W g j = W := by
  unfold p94ef_f; rw [if_pos hj]

open AllocationIndices in
private lemma p94ef_f_F {k : ℕ} (r : Fin k → ℝ) (W : ℝ) (g : Fin k → Bool) (j : ℕ)
    (hj : p94ef_G (p94ef_a g) j = false) : p94ef_f r W g j = extendReward r j := by
  unfold p94ef_f; rw [if_neg (by simp [hj])]

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset Filter AllocationIndices in
private lemma p94ef_avg_eq {k : ℕ} (nu rho r : Fin k → ℝ)
    (hnu : ∀ x, nu x ∈ Set.Icc (0 : ℝ) 1) (hrho : ∀ x, rho x ∈ Set.Icc (0 : ℝ) 1)
    (hnu_bot : ∀ x : Fin k, x.val = 0 → nu x = 0)
    (hrho_top : ∀ x : Fin k, x.val + 1 = k → rho x = 0)
    (hpsi : StrictMonoOn (vigourShare nu rho) (Set.Iic k))
    (W : ℝ) (g : Fin k → Bool) (x : Fin k) :
    avgReward (vigourBandit nu rho r hnu hrho) W g x =
      vigourValue nu rho r W (p94ef_L (p94ef_a g) x.val) := by
  unfold avgReward stationaryExpectedReward
  refine p94ef_avg (stationaryKernel (vigourBandit nu rho r hnu hrho) g)
    (subsidizedReward (vigourBandit nu rho r hnu hrho) W g)
    (fun z ↦ p94ef_c nu rho r W g z.val) (fun z ↦ p94ef_h nu rho r W g z.val) ?_ ?_ x
  · intro z
    rw [p94ef_sk_int]
    have hn := z.isLt
    have hG := p94ef_Ga g z
    cases hgz : g z
    · -- passive: moves up
      rw [hgz] at hG
      simp only [Bool.false_eq_true, if_false]
      by_cases hk : z.val + 1 < k
      · have hu : upState z = ⟨z.val + 1, hk⟩ :=
          Fin.ext (by simp [upState]; omega)
        rw [hu]
        have := p94ef_L_up (p94ef_a g) z.val (by rw [hG]; rfl) hk
        simp only [p94ef_c]
        rw [this]; ring
      · rw [hrho_top z (by omega)]; ring
    · -- active: moves down
      rw [hgz] at hG
      simp only [if_true]
      rcases Nat.eq_zero_or_pos z.val with h0 | h0
      · rw [hnu_bot z h0]; ring
      · have hd : downState z = ⟨z.val - 1, by omega⟩ :=
          Fin.ext (by simp [downState])
        rw [hd]
        have := p94ef_L_dn (p94ef_a g) z.val (by rw [hG]; rfl) h0
        simp only [p94ef_c]
        rw [this]; ring
  · intro z
    rw [p94ef_sk_int]
    have hn := z.isLt
    have hG := p94ef_Ga g z
    have hf : subsidizedReward (vigourBandit nu rho r hnu hrho) W g z = p94ef_f r W g z.val := by
      unfold p94ef_f
      rw [hG, p94ef_ext_lt r z.val hn]
      cases hgz : g z <;> simp [subsidizedReward, vigourBandit, hgz]
    rw [hf]
    cases hgz : g z
    · -- passive: moves up
      rw [hgz] at hG
      have hGt : p94ef_G (p94ef_a g) z.val = true := by rw [hG]; rfl
      simp only [Bool.false_eq_true, if_false]
      by_cases hk : z.val + 1 < k
      · have hu : upState z = ⟨z.val + 1, hk⟩ :=
          Fin.ext (by simp [upState]; omega)
        rw [hu]
        have hrz := p94ef_rho_pos nu rho hnu hrho hpsi z.val hk
        have hrz' : rho ⟨z.val, by omega⟩ = rho z := rfl
        rw [hrz'] at hrz
        have hsp := p94ef_h_split nu rho r W g z.val hk
        simp only
        rw [hsp]
        have hdd : p94ef_d nu rho r W g z.val =
            (p94ef_f r W g z.val - p94ef_c nu rho r W g z.val) / extendReward rho z.val := by
          unfold p94ef_d; rw [if_pos hGt]
        rw [hdd, p94ef_ext_lt rho z.val hn]
        have hrz'' : rho ⟨z.val, hn⟩ = rho z := rfl
        rw [hrz'']
        field_simp
        ring
      · rw [hrho_top z (by omega)]
        simp only [p94ef_c]
        rw [p94ef_L_top (p94ef_a g) z.val hGt (by omega), p94ef_Vk nu rho r W (by omega),
          p94ef_f_T r W g _ hGt]
        ring
    · -- active: moves down
      rw [hgz] at hG
      have hGf : p94ef_G (p94ef_a g) z.val = false := by rw [hG]; rfl
      simp only [if_true]
      rcases Nat.eq_zero_or_pos z.val with h0 | h0
      · rw [hnu_bot z h0]
        have hG0 : p94ef_G (p94ef_a g) 0 = false := by rw [← h0]; exact hGf
        simp only [p94ef_c]
        rw [h0, p94ef_L_zero (p94ef_a g) hG0, p94ef_V0, p94ef_f_F r W g 0 hG0]
        ring
      · have hd : downState z = ⟨z.val - 1, by omega⟩ :=
          Fin.ext (by simp [downState])
        rw [hd]
        have hvz := p94ef_nu_pos nu rho hnu hpsi z.val h0 hn
        have hsp := p94ef_h_split nu rho r W g (z.val - 1) (by omega)
        have e1 : z.val - 1 + 1 = z.val := by omega
        rw [e1] at hsp
        simp only
        rw [hsp]
        have hvz' : nu ⟨z.val, hn⟩ = nu z := rfl
        rw [hvz'] at hvz
        cases h1 : p94ef_G (p94ef_a g) (z.val - 1) with
        | true =>
          -- the pair class {z - 1, z}
          have hdd : p94ef_d nu rho r W g (z.val - 1) =
              (p94ef_f r W g (z.val - 1) - p94ef_c nu rho r W g (z.val - 1)) /
                extendReward rho (z.val - 1) := by
            unfold p94ef_d; rw [if_pos h1]
          rw [hdd]
          have hLz : p94ef_L (p94ef_a g) z.val = z.val := by
            have := p94ef_L_pair (p94ef_a g) (z.val - 1) h1 (by rw [e1]; exact hGf)
            rwa [e1] at this
          have hc1 : p94ef_c nu rho r W g (z.val - 1) = p94ef_c nu rho r W g z.val := by
            unfold p94ef_c; rw [p94ef_L_dn (p94ef_a g) z.val hGf h0]
          rw [hc1, p94ef_f_T r W g _ h1, p94ef_f_F r W g _ hGf]
          unfold p94ef_c; rw [hLz]
          unfold vigourValue
          rw [p94ef_share_mid nu rho z.val h0 hn, p94ef_ext_lt rho (z.val - 1) (by omega),
            p94ef_ext_lt r z.val hn]
          have hrl := p94ef_rho_pos nu rho hnu hrho hpsi (z.val - 1) (by omega)
          have hvz'' : nu ⟨z.val, hn⟩ = nu z := rfl
          rw [hvz'']
          set m := rho ⟨z.val - 1, by omega⟩ with hm_def
          set l := nu z with hl_def
          set b := r ⟨z.val, hn⟩
          have hlm : 0 < l + m := by linarith
          field_simp
          ring
        | false =>
          have hdd : p94ef_d nu rho r W g (z.val - 1) =
              -((p94ef_f r W g z.val - p94ef_c nu rho r W g z.val) / extendReward nu z.val) := by
            unfold p94ef_d; rw [if_neg (by simp [h1]), e1, if_pos hGf]
          rw [hdd, p94ef_ext_lt nu z.val hn]
          have hvz'' : nu ⟨z.val, hn⟩ = nu z := rfl
          rw [hvz'']
          field_simp
          ring

/-! ### The optimal average reward, optimal policies and the passive set -/

open AllocationIndices in
private noncomputable def p94ef_E {k : ℕ} (nu rho r : Fin k → ℝ) (W : ℝ) : ℝ :=
  (Finset.range (k + 1)).sup' (by simp) fun y ↦ vigourValue nu rho r W y

open AllocationIndices in
private lemma p94ef_V_le {k : ℕ} (nu rho r : Fin k → ℝ) (W : ℝ) (y : ℕ) (hy : y ≤ k) :
    vigourValue nu rho r W y ≤ p94ef_E nu rho r W := by
  unfold p94ef_E
  exact Finset.le_sup' (fun y ↦ vigourValue nu rho r W y) (Finset.mem_range.2 (by omega))

open AllocationIndices in
private lemma p94ef_V_ex {k : ℕ} (nu rho r : Fin k → ℝ) (W : ℝ) :
    ∃ y, y ≤ k ∧ vigourValue nu rho r W y = p94ef_E nu rho r W := by
  obtain ⟨y, hy, hyM⟩ := Finset.exists_mem_eq_sup' (s := Finset.range (k + 1)) (by simp)
    (fun y ↦ vigourValue nu rho r W y)
  refine ⟨y, by simp at hy; omega, ?_⟩
  unfold p94ef_E
  exact hyM.symm

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices in
private lemma p94ef_opt {k : ℕ} (nu rho r : Fin k → ℝ)
    (hnu : ∀ x, nu x ∈ Set.Icc (0 : ℝ) 1) (hrho : ∀ x, rho x ∈ Set.Icc (0 : ℝ) 1)
    (hnu_bot : ∀ x : Fin k, x.val = 0 → nu x = 0)
    (hrho_top : ∀ x : Fin k, x.val + 1 = k → rho x = 0)
    (hpsi : StrictMonoOn (vigourShare nu rho) (Set.Iic k)) (hk : 0 < k) (W : ℝ) :
    optimalAvg (vigourBandit nu rho r hnu hrho) W = p94ef_E nu rho r W := by
  have hne : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  unfold optimalAvg
  apply le_antisymm
  · refine ciSup_le fun g ↦ ciSup_le fun x ↦ ?_
    rw [p94ef_avg_eq nu rho r hnu hrho hnu_bot hrho_top hpsi]
    exact p94ef_V_le nu rho r W _ (p94ef_L_le (p94ef_a g) x.val x.isLt)
  · obtain ⟨y, hyk, hyM⟩ := p94ef_V_ex nu rho r W
    rw [← hyM]
    have h1 : vigourValue nu rho r W y =
        avgReward (vigourBandit nu rho r hnu hrho) W (vigourThreshold (k := k) y) ⟨0, hk⟩ := by
      rw [p94ef_avg_eq nu rho r hnu hrho hnu_bot hrho_top hpsi, p94ef_a_thr, p94ef_L_thr y hyk]
    rw [h1]
    refine le_ciSup_of_le (Set.finite_range _).bddAbove (vigourThreshold (k := k) y) ?_
    exact le_ciSup_of_le (Set.finite_range _).bddAbove ⟨0, hk⟩ le_rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices in
private lemma p94ef_passive {k : ℕ} (nu rho r : Fin k → ℝ)
    (hnu : ∀ x, nu x ∈ Set.Icc (0 : ℝ) 1) (hrho : ∀ x, rho x ∈ Set.Icc (0 : ℝ) 1)
    (hnu_bot : ∀ x : Fin k, x.val = 0 → nu x = 0)
    (hrho_top : ∀ x : Fin k, x.val + 1 = k → rho x = 0)
    (hpsi : StrictMonoOn (vigourShare nu rho) (Set.Iic k)) (hk : 0 < k) (W : ℝ) (x : Fin k) :
    x ∈ passiveSet (vigourBandit nu rho r hnu hrho) W ↔
      ∃ y, x.val < y ∧ y ≤ k ∧ vigourValue nu rho r W y = p94ef_E nu rho r W := by
  unfold passiveSet IsAvgOptimal
  simp only [Set.mem_ofPred_eq, p94ef_avg_eq nu rho r hnu hrho hnu_bot hrho_top hpsi,
    p94ef_opt nu rho r hnu hrho hnu_bot hrho_top hpsi hk]
  constructor
  · rintro ⟨g, hg, hgx⟩
    have hGt : p94ef_G (p94ef_a g) x.val = true := by rw [p94ef_Ga, hgx]; rfl
    have hL : p94ef_L (p94ef_a g) x.val = p94ef_Lup (p94ef_a g) x.val := by
      unfold p94ef_L; rw [if_pos hGt]
    refine ⟨p94ef_L (p94ef_a g) x.val, ?_, p94ef_L_le (p94ef_a g) x.val x.isLt, hg x⟩
    rw [hL]; exact (p94ef_Lup_spec (p94ef_a g) x.val).1
  · rintro ⟨y, hxy, hyk, hV⟩
    refine ⟨vigourThreshold (k := k) y, fun z ↦ ?_, ?_⟩
    · rw [p94ef_a_thr, p94ef_L_thr y hyk]; exact hV
    · unfold vigourThreshold; simp only [decide_eq_false_iff_not, not_le]; exact hxy

open AllocationIndices in
private lemma p94ef_cmp {k : ℕ} (nu rho r : Fin k → ℝ)
    (hpsi : StrictMonoOn (vigourShare nu rho) (Set.Iic k)) (W : ℝ) (y : Fin k) :
    vigourValue nu rho r W y.val ≤ vigourValue nu rho r W (y.val + 1) ↔
      vigourIndex nu rho r y ≤ W := by
  have hd := p94ef_share_strict nu rho hpsi y.val (y.val + 1) (by omega)
    (by have := y.isLt; omega)
  have hpos : 0 < vigourShare nu rho (y.val + 1) - vigourShare nu rho y.val := by linarith
  unfold vigourIndex vigourValue
  rw [div_le_iff₀ hpos]
  constructor <;> intro h <;> nlinarith

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices in
theorem solution {k : ℕ} (nu rho r : Fin k → ℝ)
    (hnu : ∀ x, nu x ∈ Set.Icc (0 : ℝ) 1) (hrho : ∀ x, rho x ∈ Set.Icc (0 : ℝ) 1)
    (hnu_bot : ∀ x : Fin k, x.val = 0 → nu x = 0)
    (hrho_top : ∀ x : Fin k, x.val + 1 = k → rho x = 0)
    (hr : Monotone r) (hr0 : ∀ x, 0 ≤ r x)
    (hpsi : StrictMonoOn (vigourShare nu rho) (Set.Iic k)) :
    Indexable (vigourBandit nu rho r hnu hrho) ∧
    (StrictMono (vigourIndex nu rho r) →
      ∀ x, whittleIndex (vigourBandit nu rho r hnu hrho) x = vigourIndex nu rho r x) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    exact ⟨fun _ _ _ x ↦ x.elim0, fun _ x ↦ x.elim0⟩
  have hP := p94ef_passive nu rho r hnu hrho hnu_bot hrho_top hpsi hk
  refine ⟨fun W W' hWW' x hx ↦ ?_, fun hmono x ↦ ?_⟩
  · -- indexability
    rw [hP] at hx ⊢
    obtain ⟨y, hxy, hyk, hyV⟩ := hx
    obtain ⟨y', hy'k, hy'V⟩ := p94ef_V_ex nu rho r W'
    by_cases hyy : x.val < y'
    · exact ⟨y', hyy, hy'k, hy'V⟩
    · refine ⟨y, hxy, hyk, le_antisymm (p94ef_V_le nu rho r W' y hyk) ?_⟩
      rw [← hy'V]
      have hs := p94ef_share_strict nu rho hpsi y' y (by omega) hyk
      have h1 := p94ef_V_le nu rho r W y' hy'k
      rw [← hyV] at h1
      have hm := mul_nonneg (sub_nonneg.2 hWW') (sub_nonneg.2 hs.le)
      unfold vigourValue at h1 ⊢
      nlinarith
  · -- the Whittle index
    have hset : {W : ℝ | x ∈ passiveSet (vigourBandit nu rho r hnu hrho) W} =
        Set.Ici (vigourIndex nu rho r x) := by
      ext W
      simp only [Set.mem_ofPred_eq, Set.mem_Ici, hP]
      constructor
      · rintro ⟨y, hxy, hyk, hyV⟩
        have hy1 : y - 1 < k := by omega
        have e : y - 1 + 1 = y := by omega
        have h1 : vigourValue nu rho r W ((⟨y - 1, hy1⟩ : Fin k).val) ≤
            vigourValue nu rho r W ((⟨y - 1, hy1⟩ : Fin k).val + 1) := by
          show vigourValue nu rho r W (y - 1) ≤ vigourValue nu rho r W (y - 1 + 1)
          rw [e, hyV]; exact p94ef_V_le nu rho r W _ (by omega)
        rw [p94ef_cmp nu rho r hpsi W ⟨y - 1, hy1⟩] at h1
        exact le_trans (hmono.monotone (show x ≤ (⟨y - 1, hy1⟩ : Fin k) from
          Fin.le_def.2 (by simp only; omega))) h1
      · intro hW
        have hxk : x.val + 1 ≤ k := x.isLt
        -- below `x + 1` the thresholds only gain
        have hasc : ∀ d, d ≤ x.val + 1 →
            vigourValue nu rho r W (x.val + 1 - d) ≤ vigourValue nu rho r W (x.val + 1) := by
          intro d
          induction d with
          | zero => intro _; simp
          | succ d ih =>
            intro hd
            have hj : x.val - d < k := by omega
            have e1 : x.val + 1 - (d + 1) = x.val - d := by omega
            have e2 : x.val - d + 1 = x.val + 1 - d := by omega
            have h2 : vigourIndex nu rho r ⟨x.val - d, hj⟩ ≤ W :=
              le_trans (hmono.monotone (show (⟨x.val - d, hj⟩ : Fin k) ≤ x from
                Fin.le_def.2 (by simp only; omega))) hW
            rw [← p94ef_cmp nu rho r hpsi W ⟨x.val - d, hj⟩] at h2
            simp only at h2
            rw [e1]
            rw [e2] at h2
            exact le_trans h2 (ih (by omega))
        obtain ⟨y, hy, hyM⟩ := Finset.exists_mem_eq_sup' (s := Finset.Icc (x.val + 1) k)
          (⟨x.val + 1, Finset.mem_Icc.2 ⟨le_rfl, hxk⟩⟩)
          (fun y ↦ vigourValue nu rho r W y)
        have hy' := Finset.mem_Icc.1 hy
        have hle : ∀ j, j ∈ Finset.Icc (x.val + 1) k →
            vigourValue nu rho r W j ≤ vigourValue nu rho r W y := by
          intro j hj
          rw [← hyM]
          exact Finset.le_sup' (fun y ↦ vigourValue nu rho r W y) hj
        refine ⟨y, by omega, hy'.2, le_antisymm (p94ef_V_le nu rho r W y hy'.2) ?_⟩
        unfold p94ef_E
        refine Finset.sup'_le _ _ fun j hj ↦ ?_
        have hjk : j ≤ k := by simp at hj; omega
        show vigourValue nu rho r W j ≤ vigourValue nu rho r W y
        by_cases hjx : j ≤ x.val + 1
        · have := hasc (x.val + 1 - j) (by omega)
          have e3 : x.val + 1 - (x.val + 1 - j) = j := by omega
          rw [e3] at this
          exact le_trans this (hle _ (Finset.mem_Icc.2 ⟨le_rfl, hxk⟩))
        · exact hle j (Finset.mem_Icc.2 ⟨by omega, hjk⟩)
    unfold whittleIndex
    rw [hset, csInf_Ici]
