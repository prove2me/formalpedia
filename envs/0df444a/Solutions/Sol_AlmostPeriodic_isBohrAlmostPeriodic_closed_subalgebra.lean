-- Prove2me | solution 1 for AlmostPeriodic.isBohrAlmostPeriodic_closed_subalgebra
-- status  : ACCEPTED   (prove)
-- author  : @WalrusPaul
-- created : 2026-11-22T18:49:50.021089+00:00
-- url     : https://prove2.me/submissions/d80e9f35-03fa-4139-9cb1-d51b87e19906

import Mathlib
import Definitions.Def_AlmostPeriodic_BohrAlmostPeriodic

open Filter Topology

set_option autoImplicit false

open AlmostPeriodic

lemma apx_relDense_mono {A B : Set ℝ} (hAB : A ⊆ B) (hA : IsRelativelyDense A) :
    IsRelativelyDense B := by
  obtain ⟨L, hL, h⟩ := hA
  exact ⟨L, hL, fun a => (h a).mono (Set.inter_subset_inter_left _ hAB)⟩

lemma apx_relDense_len {A : Set ℝ} {L L' : ℝ} (hLL' : L ≤ L')
    (h : ∀ a, (A ∩ Set.Icc a (a + L)).Nonempty) : ∀ a, (A ∩ Set.Icc a (a + L')).Nonempty := by
  intro a
  obtain ⟨t, ht, ht1, ht2⟩ := h a
  exact ⟨t, ht, ht1, by linarith⟩

lemma apx_bounded {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : IsBohrAlmostPeriodic f) : ∃ M, 0 < M ∧ ∀ x, ‖f x‖ ≤ M := by
  obtain ⟨hc, hp⟩ := hf
  obtain ⟨L, hL, h⟩ := hp 1 one_pos
  obtain ⟨M0, hM0⟩ :=
    (isCompact_Icc (a := (0:ℝ)) (b := L)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max M0 0 + 1, by positivity, fun x => ?_⟩
  obtain ⟨τ, hτ, h1, h2⟩ := h (-x)
  have hτ' : ∀ y, ‖f (y + τ) - f y‖ ≤ 1 := hτ
  have hy : x + τ ∈ Set.Icc (0:ℝ) L := ⟨by linarith, by linarith⟩
  have e1 := hM0 _ hy
  have e2 := hτ' x
  have key : f x = f (x + τ) - (f (x + τ) - f x) := by abel
  rw [key]
  have := norm_sub_le (f (x + τ)) (f (x + τ) - f x)
  linarith [le_max_left M0 0]

lemma apx_unifCont {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : IsBohrAlmostPeriodic f) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ ∀ x t : ℝ, |t| < δ → ‖f (x + t) - f x‖ ≤ ε := by
  obtain ⟨hc, hp⟩ := hf
  obtain ⟨L, hL, hT⟩ := hp (ε/3) (by positivity)
  have hUC : UniformContinuousOn f (Set.Icc (-1:ℝ) (L+1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hc.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨δ', hδ', hU⟩ := hUC (ε/3) (by positivity)
  refine ⟨min δ' 1, by positivity, fun x t ht => ?_⟩
  obtain ⟨τ, hτ, h1, h2⟩ := hT (-x)
  have hτ' : ∀ y, ‖f (y + τ) - f y‖ ≤ ε/3 := hτ
  have ht1 : |t| < δ' := lt_of_lt_of_le ht (min_le_left _ _)
  have ht2 : |t| < 1 := lt_of_lt_of_le ht (min_le_right _ _)
  have habs := abs_lt.mp ht2
  have hy : x + τ ∈ Set.Icc (-1:ℝ) (L+1) := ⟨by linarith, by linarith⟩
  have hyt : x + τ + t ∈ Set.Icc (-1:ℝ) (L+1) := ⟨by linarith, by linarith⟩
  have hd : dist (x + τ + t) (x + τ) < δ' := by
    rw [Real.dist_eq]; simpa using ht1
  have e1 : ‖f (x + τ + t) - f (x + τ)‖ < ε/3 := by
    have := hU _ hyt _ hy hd
    rwa [dist_eq_norm] at this
  have e2 : ‖f (x + t + τ) - f (x + t)‖ ≤ ε/3 := hτ' (x + t)
  have e3 : ‖f (x + τ) - f x‖ ≤ ε/3 := hτ' x
  have eq : x + t + τ = x + τ + t := by ring
  rw [eq] at e2
  have key : f (x + t) - f x =
      (f (x + τ + t) - f (x + τ)) - (f (x + τ + t) - f (x + t)) + (f (x + τ) - f x) := by abel
  rw [key]
  have t1 := norm_add_le ((f (x + τ + t) - f (x + τ)) - (f (x + τ + t) - f (x + t)))
    (f (x + τ) - f x)
  have t2 := norm_sub_le (f (x + τ + t) - f (x + τ)) (f (x + τ + t) - f (x + t))
  linarith

lemma apx_common {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : ℝ → E}
    {g : ℝ → F} (hf : IsBohrAlmostPeriodic f) (hg : IsBohrAlmostPeriodic g) (ε : ℝ)
    (hε : 0 < ε) :
    IsRelativelyDense
      {τ : ℝ | (∀ x, ‖f (x + τ) - f x‖ ≤ ε) ∧ (∀ x, ‖g (x + τ) - g x‖ ≤ ε)} := by
  obtain ⟨η, hη⟩ : ∃ η, η = ε / 3 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  obtain ⟨δ, hδ, hgu⟩ := apx_unifCont hg η hη0
  obtain ⟨Lf, hLf, hTf⟩ := hf.2 η hη0
  obtain ⟨Lg, hLg, hTg⟩ := hg.2 η hη0
  obtain ⟨L, hLdef⟩ : ∃ L, L = max Lf Lg := ⟨_, rfl⟩
  have hL : 0 < L := hLdef ▸ lt_max_of_lt_left hLf
  have hTf' := apx_relDense_len (hLdef ▸ le_max_left Lf Lg) hTf
  have hTg' := apx_relDense_len (hLdef ▸ le_max_right Lf Lg) hTg
  have hrep : ∀ k : ℤ, ∃ p : ℝ × ℝ,
      (∃ q : ℝ × ℝ, (∀ x, ‖f (x + q.1) - f x‖ ≤ η) ∧ (∀ x, ‖g (x + q.2) - g x‖ ≤ η) ∧
        ⌊(q.1 - q.2) / δ⌋ = k) →
      (∀ x, ‖f (x + p.1) - f x‖ ≤ η) ∧ (∀ x, ‖g (x + p.2) - g x‖ ≤ η) ∧
        ⌊(p.1 - p.2) / δ⌋ = k := by
    intro k
    by_cases hk : ∃ q : ℝ × ℝ, (∀ x, ‖f (x + q.1) - f x‖ ≤ η) ∧
        (∀ x, ‖g (x + q.2) - g x‖ ≤ η) ∧ ⌊(q.1 - q.2) / δ⌋ = k
    · obtain ⟨q, hq⟩ := hk
      exact ⟨q, fun _ => hq⟩
    · exact ⟨(0, 0), fun h => absurd h hk⟩
  choose rep hrep using hrep
  obtain ⟨S, hS⟩ : ∃ S : Finset ℤ, S = Finset.Icc ⌊-L / δ⌋ ⌊L / δ⌋ := ⟨_, rfl⟩
  obtain ⟨K, hK0, hKk⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ k ∈ S, |(rep k).1| ≤ K :=
    ⟨∑ k ∈ S, |(rep k).1|, Finset.sum_nonneg (fun k _ => abs_nonneg _),
      fun k hk => Finset.single_le_sum (f := fun k => |(rep k).1|)
        (fun k _ => abs_nonneg _) hk⟩
  refine ⟨L + 2 * K, by linarith, fun b => ?_⟩
  obtain ⟨τ₁, hτ₁, hτ₁a, hτ₁b⟩ := hTf' (b + K)
  obtain ⟨τ₂, hτ₂, hτ₂a, hτ₂b⟩ := hTg' (b + K)
  have hτ₁' : ∀ x, ‖f (x + τ₁) - f x‖ ≤ η := hτ₁
  have hτ₂' : ∀ x, ‖g (x + τ₂) - g x‖ ≤ η := hτ₂
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = ⌊(τ₁ - τ₂) / δ⌋ := ⟨_, rfl⟩
  have hPk : ∃ q : ℝ × ℝ, (∀ x, ‖f (x + q.1) - f x‖ ≤ η) ∧ (∀ x, ‖g (x + q.2) - g x‖ ≤ η) ∧
      ⌊(q.1 - q.2) / δ⌋ = k := ⟨(τ₁, τ₂), hτ₁', hτ₂', hk.symm⟩
  obtain ⟨hσ₁, hσ₂, hσk⟩ := hrep k hPk
  have hkS : k ∈ S := by
    rw [hS, Finset.mem_Icc, hk]
    constructor
    · apply Int.floor_mono
      apply div_le_div_of_nonneg_right _ hδ.le
      linarith
    · apply Int.floor_mono
      apply div_le_div_of_nonneg_right _ hδ.le
      linarith
  have hσ₁K : |(rep k).1| ≤ K := hKk k hkS
  generalize (rep k).1 = σ₁ at hσ₁ hσk hσ₁K
  generalize (rep k).2 = σ₂ at hσ₂ hσk
  have hdiff : |(τ₁ - τ₂) / δ - (σ₁ - σ₂) / δ| < 1 :=
    Int.abs_sub_lt_one_of_floor_eq_floor (hk.symm.trans hσk.symm)
  have hhδ : |(τ₁ - τ₂) - (σ₁ - σ₂)| < δ := by
    rw [← sub_div, abs_div, abs_of_pos hδ, div_lt_one hδ] at hdiff
    exact hdiff
  have hσ₁b := abs_le.mp hσ₁K
  refine ⟨τ₁ - σ₁, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro x
    have e1 := hτ₁' (x - σ₁)
    have e2 := hσ₁ (x - σ₁)
    have q1 : x - σ₁ + τ₁ = x + (τ₁ - σ₁) := by ring
    have q2 : x - σ₁ + σ₁ = x := by ring
    rw [q1] at e1
    rw [q2] at e2
    have key : f (x + (τ₁ - σ₁)) - f x =
        (f (x + (τ₁ - σ₁)) - f (x - σ₁)) - (f x - f (x - σ₁)) := by abel
    rw [key]
    have := norm_sub_le (f (x + (τ₁ - σ₁)) - f (x - σ₁)) (f x - f (x - σ₁))
    linarith
  · intro x
    have e1 := hgu (x + (τ₂ - σ₂)) ((τ₁ - τ₂) - (σ₁ - σ₂)) hhδ
    have e2 := hτ₂' (x - σ₂)
    have e3 := hσ₂ (x - σ₂)
    have q0 : x + (τ₂ - σ₂) + ((τ₁ - τ₂) - (σ₁ - σ₂)) = x + (τ₁ - σ₁) := by ring
    have q1 : x - σ₂ + τ₂ = x + (τ₂ - σ₂) := by ring
    have q2 : x - σ₂ + σ₂ = x := by ring
    rw [q0] at e1
    rw [q1] at e2
    rw [q2] at e3
    have key : g (x + (τ₁ - σ₁)) - g x =
        (g (x + (τ₁ - σ₁)) - g (x + (τ₂ - σ₂))) +
          ((g (x + (τ₂ - σ₂)) - g (x - σ₂)) - (g x - g (x - σ₂))) := by abel
    rw [key]
    have t1 := norm_add_le (g (x + (τ₁ - σ₁)) - g (x + (τ₂ - σ₂)))
      ((g (x + (τ₂ - σ₂)) - g (x - σ₂)) - (g x - g (x - σ₂)))
    have t2 := norm_sub_le (g (x + (τ₂ - σ₂)) - g (x - σ₂)) (g x - g (x - σ₂))
    linarith
  · linarith
  · linarith

theorem solution {R : Type*} [NormedRing R] :
    (∀ c : R, IsBohrAlmostPeriodic (fun _ : ℝ => c)) ∧
    (∀ f g : ℝ → R, IsBohrAlmostPeriodic f → IsBohrAlmostPeriodic g →
      IsBohrAlmostPeriodic (fun x => f x + g x)) ∧
    (∀ f g : ℝ → R, IsBohrAlmostPeriodic f → IsBohrAlmostPeriodic g →
      IsBohrAlmostPeriodic (fun x => f x * g x)) ∧
    (∀ (F : ℕ → ℝ → R) (f : ℝ → R), (∀ n : ℕ, IsBohrAlmostPeriodic (F n)) →
      TendstoUniformly F f atTop → IsBohrAlmostPeriodic f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    refine ⟨continuous_const, fun ε hε => ⟨1, one_pos, fun a => ⟨a, ?_, le_refl a, by linarith⟩⟩⟩
    show ∀ x : ℝ, ‖c - c‖ ≤ ε
    intro x
    simp [hε.le]
  · intro f g hf hg
    refine ⟨hf.1.add hg.1, fun ε hε => ?_⟩
    apply apx_relDense_mono _ (apx_common hf hg (ε / 2) (by positivity))
    intro τ hτ
    obtain ⟨h1, h2⟩ := hτ
    show ∀ x, ‖f (x + τ) + g (x + τ) - (f x + g x)‖ ≤ ε
    intro x
    have key : f (x + τ) + g (x + τ) - (f x + g x) = (f (x + τ) - f x) + (g (x + τ) - g x) := by
      abel
    rw [key]
    have := norm_add_le (f (x + τ) - f x) (g (x + τ) - g x)
    linarith [h1 x, h2 x]
  · intro f g hf hg
    obtain ⟨Mf, hMf, hfb⟩ := apx_bounded hf
    obtain ⟨Mg, hMg, hgb⟩ := apx_bounded hg
    refine ⟨hf.1.mul hg.1, fun ε hε => ?_⟩
    apply apx_relDense_mono _ (apx_common hf hg (ε / (Mf + Mg)) (by positivity))
    intro τ hτ
    obtain ⟨h1, h2⟩ := hτ
    show ∀ x, ‖f (x + τ) * g (x + τ) - f x * g x‖ ≤ ε
    intro x
    have key : f (x + τ) * g (x + τ) - f x * g x =
        f (x + τ) * (g (x + τ) - g x) + (f (x + τ) - f x) * g x := by
      noncomm_ring
    rw [key]
    have t1 := norm_add_le (f (x + τ) * (g (x + τ) - g x)) ((f (x + τ) - f x) * g x)
    have t2 := norm_mul_le (f (x + τ)) (g (x + τ) - g x)
    have t3 := norm_mul_le (f (x + τ) - f x) (g x)
    have b1 : ‖f (x + τ)‖ * ‖g (x + τ) - g x‖ ≤ Mf * (ε / (Mf + Mg)) :=
      mul_le_mul (hfb _) (h2 x) (norm_nonneg _) hMf.le
    have b2 : ‖f (x + τ) - f x‖ * ‖g x‖ ≤ (ε / (Mf + Mg)) * Mg :=
      mul_le_mul (h1 x) (hgb x) (norm_nonneg _) (by positivity)
    have b3 : Mf * (ε / (Mf + Mg)) + (ε / (Mf + Mg)) * Mg = ε := by
      field_simp
    linarith
  · intro F f hF hFf
    refine ⟨hFf.continuous (Frequently.of_forall fun n => (hF n).1), fun ε hε => ?_⟩
    rw [Metric.tendstoUniformly_iff] at hFf
    obtain ⟨n, hn⟩ := (hFf (ε / 3) (by positivity)).exists
    apply apx_relDense_mono _ ((hF n).2 (ε / 3) (by positivity))
    intro τ hτ
    have hτ' : ∀ x, ‖F n (x + τ) - F n x‖ ≤ ε / 3 := hτ
    show ∀ x, ‖f (x + τ) - f x‖ ≤ ε
    intro x
    have e1 := hn (x + τ)
    have e2 := hn x
    have e3 := hτ' x
    rw [dist_eq_norm] at e1 e2
    have key : f (x + τ) - f x =
        (f (x + τ) - F n (x + τ)) + (F n (x + τ) - F n x) - (f x - F n x) := by abel
    rw [key]
    have t1 := norm_sub_le ((f (x + τ) - F n (x + τ)) + (F n (x + τ) - F n x)) (f x - F n x)
    have t2 := norm_add_le (f (x + τ) - F n (x + τ)) (F n (x + τ) - F n x)
    linarith
