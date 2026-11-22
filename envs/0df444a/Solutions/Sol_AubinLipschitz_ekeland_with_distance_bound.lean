-- Prove2me | solution 1 for AubinLipschitz.ekeland_with_distance_bound
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T07:50:46.197791+00:00
-- url     : https://prove2.me/submissions/1e6ca174-c4d5-424a-97a9-23928586ebb4

import Mathlib

open Filter Set
open scoped Topology

theorem solution {Z : Type*} [MetricSpace Z] [CompleteSpace Z] (f : Z → ℝ)
    (hf : LowerSemicontinuous f) (m : ℝ) (hm : ∀ z, m ≤ f z) (ε : ℝ) (hε : 0 < ε) (z₁ : Z) :
    ∃ zbar : Z, f zbar + ε * dist zbar z₁ ≤ f z₁ ∧ ∀ z : Z, f zbar ≤ f z + ε * dist zbar z := by
  classical
  -- The Ekeland ball around a point.
  let Φ : Z → Set Z := fun x => {y | f y + ε * dist y x ≤ f x}
  have hΦ_mem : ∀ x, x ∈ Φ x := fun x => by simp [Φ, dist_self]
  have hΦ_bdd : ∀ x, BddBelow (f '' Φ x) := fun x =>
    ⟨m, by rintro _ ⟨y, -, rfl⟩; exact hm y⟩
  have hΦ_closed : ∀ x, IsClosed (Φ x) := by
    intro x
    have hlsc : LowerSemicontinuous fun y : Z => f y + ε * dist y x :=
      hf.add ((continuous_id.dist continuous_const).const_mul ε).lowerSemicontinuous
    exact hlsc.isClosed_preimage (f x)
  -- Approximate minimisers of `f` on each Ekeland ball.
  have hex : ∀ (x : Z) (n : ℕ), ∃ y ∈ Φ x, f y < sInf (f '' Φ x) + ε * (1 / 2 : ℝ) ^ (n + 1) := by
    intro x n
    have hη : 0 < ε * (1 / 2 : ℝ) ^ (n + 1) := by positivity
    obtain ⟨v, hv, hlt⟩ :=
      exists_lt_of_csInf_lt (s := f '' (Φ x)) ⟨f x, x, hΦ_mem x, rfl⟩ (lt_add_of_pos_right _ hη)
    obtain ⟨y, hy, rfl⟩ := hv
    exact ⟨y, hy, hlt⟩
  -- The recursively chosen sequence.
  let x : ℕ → Z := fun n => Nat.rec z₁ (fun n ih => Classical.choose (hex ih n)) n
  have hx0 : x 0 = z₁ := rfl
  have hxsucc : ∀ n, x (n + 1) = Classical.choose (hex (x n) n) := fun n => rfl
  have hxmem : ∀ n, x (n + 1) ∈ Φ (x n) := fun n => by
    rw [hxsucc n]
    exact (Classical.choose_spec (hex (x n) n)).1
  have hxlt : ∀ n, f (x (n + 1)) < sInf (f '' Φ (x n)) + ε * (1 / 2 : ℝ) ^ (n + 1) := fun n => by
    rw [hxsucc n]
    exact (Classical.choose_spec (hex (x n) n)).2
  -- Approximate minimality.
  have hmin : ∀ n y, y ∈ Φ (x n) → f (x (n + 1)) ≤ f y + ε * (1 / 2 : ℝ) ^ (n + 1) := by
    intro n y hy
    have h1 := hxlt n
    have h2 : sInf (f '' Φ (x n)) ≤ f y := csInf_le (hΦ_bdd (x n)) ⟨y, hy, rfl⟩
    linarith
  -- The Ekeland order is transitive.
  have htrans : ∀ {y x z : Z}, y ∈ Φ x → z ∈ Φ y → z ∈ Φ x := by
    intro y x z hy hz
    have htri : dist z x ≤ dist z y + dist y x := dist_triangle z y x
    have h1 : ε * dist z x ≤ ε * (dist z y + dist y x) :=
      mul_le_mul_of_nonneg_left htri hε.le
    have h2 : f z + ε * dist z y ≤ f y := hz
    have h3 : f y + ε * dist y x ≤ f x := hy
    show f z + ε * dist z x ≤ f x
    nlinarith
  -- Later points remain in all earlier balls.
  have hchain : ∀ n k, k ≤ n → x n ∈ Φ (x k) := by
    intro n k hkn
    induction n, hkn using Nat.le_induction with
    | base => exact hΦ_mem _
    | succ n hkn ih => exact htrans ih (hxmem n)
  -- Contraction: all later points are within `(1/2)^n` of `x n`.
  have hbound : ∀ n, 0 < n → ∀ y ∈ Φ (x n), dist y (x n) ≤ (1 / 2 : ℝ) ^ n := by
    intro n hn y hy
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hyk : y ∈ Φ (x k) := htrans (hxmem k) hy
    have h1 : f (x (k + 1)) ≤ f y + ε * (1 / 2 : ℝ) ^ (k + 1) := hmin k y hyk
    have h2 : f y + ε * dist y (x (k + 1)) ≤ f (x (k + 1)) := hy
    have h3 : ε * dist y (x (k + 1)) ≤ ε * (1 / 2 : ℝ) ^ (k + 1) := by linarith
    exact le_of_mul_le_mul_left h3 hε
  -- Cauchy sequence.
  have hcauchy : CauchySeq x := by
    rw [Metric.cauchySeq_iff']
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨max N 1, ?_⟩
    intro n hn
    have hM : 1 ≤ max N 1 := le_max_right N 1
    have h1 : dist (x n) (x (max N 1)) ≤ (1 / 2 : ℝ) ^ (max N 1) :=
      hbound (max N 1) hM (x n) (hchain n (max N 1) hn)
    have h2 : (1 / 2 : ℝ) ^ (max N 1) ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_left N 1)
    linarith
  obtain ⟨zbar, hzbar⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- The limit lies in the initial ball.
  have hzbar_mem : zbar ∈ Φ z₁ := by
    refine (hΦ_closed z₁).mem_of_tendsto hzbar ?_
    filter_upwards with n
    cases n with
    | zero => exact hΦ_mem z₁
    | succ n => exact hchain (n + 1) 0 (Nat.zero_le _)
  refine ⟨zbar, hzbar_mem, ?_⟩
  intro z
  by_contra hcon
  push_neg at hcon
  have hstrict : f z + ε * dist z zbar < f zbar := by
    simpa [dist_comm] using hcon
  set δ : ℝ := (f zbar - (f z + ε * dist z zbar)) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδ' : f z + ε * dist z zbar + δ < f zbar := by rw [hδdef]; linarith
  -- Eventually `f (x n) > f zbar - δ / 2`.
  have hev_f : ∀ᶠ n in atTop, f zbar - δ / 2 < f (x n) := by
    have hopen : IsOpen ((f ⁻¹' Iic (f zbar - δ / 2))ᶜ) :=
      (hf.isClosed_preimage (f zbar - δ / 2)).isOpen_compl
    have hmem : zbar ∈ ((f ⁻¹' Iic (f zbar - δ / 2))ᶜ) := by
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_Iic, not_le]
      linarith
    filter_upwards [hzbar.eventually (hopen.mem_nhds hmem)] with n hn
    simpa using hn
  -- Eventually `dist z (x n)` is close to `dist z zbar`.
  have hev_d : ∀ᶠ n in atTop, dist z (x n) ≤ dist z zbar + δ / (2 * ε) := by
    have hcont : Tendsto (fun n => dist z (x n)) atTop (𝓝 (dist z zbar)) :=
      ((continuous_const.dist continuous_id).tendsto zbar).comp hzbar
    have hpos : 0 < δ / (2 * ε) := by positivity
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hcont (δ / (2 * ε)) hpos
    filter_upwards [eventually_ge_atTop N] with n hn
    have h1 : |dist z (x n) - dist z zbar| < δ / (2 * ε) := by
      simpa [Real.dist_eq] using hN n hn
    linarith [(abs_lt.mp h1).2]
  -- Eventually `z` lies in the ball around `x n`.
  have hev_mem : ∀ᶠ n in atTop, z ∈ Φ (x n) := by
    filter_upwards [hev_f, hev_d, eventually_ge_atTop 1] with n hf' hd' _
    have h1 : ε * dist z (x n) ≤ ε * (dist z zbar + δ / (2 * ε)) :=
      mul_le_mul_of_nonneg_left hd' hε.le
    have h2 : ε * (δ / (2 * ε)) = δ / 2 := by
      field_simp
    have h3 : f z + ε * dist z (x n) ≤ f z + ε * dist z zbar + δ / 2 := by
      linarith
    show f z + ε * dist z (x n) ≤ f (x n)
    linarith
  have hev_bound : ∀ᶠ n in atTop, dist z (x n) ≤ (1 / 2 : ℝ) ^ n := by
    filter_upwards [hev_mem, eventually_ge_atTop 1] with n hmem hn1
    exact hbound n hn1 z hmem
  have hzero_tend : Tendsto (fun n => dist z (x n)) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => dist_nonneg) hev_bound ?_
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim : Tendsto (fun n => dist z (x n)) atTop (𝓝 (dist z zbar)) :=
    ((continuous_const.dist continuous_id).tendsto zbar).comp hzbar
  have hdzero : dist z zbar = 0 := tendsto_nhds_unique hlim hzero_tend
  have hzeq : z = zbar := dist_eq_zero.mp hdzero
  subst hzeq
  simp only [dist_self, mul_zero, add_zero] at hstrict
  exact lt_irrefl _ hstrict

