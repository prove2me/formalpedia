-- Prove2me | solution 1 for AugLagLLC.KKT.eq_4_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:56:27.708862+00:00
-- url     : https://prove2.me/submissions/776b99d0-1ea3-4c25-9cd5-c77c6bd5b369

import Mathlib
import Definitions.Def_AugLagLLC_KKT_Setting

open Filter Topology

open AugLagLLC.KKT in
theorem solution {n m1 p1 m2 p2 : ℕ} (P : Problem n m1 p1 m2 p2) (hP : P.IsC1)
    {τ γ ρ1 : ℝ} {lamMin lamMax : Fin m1 → ℝ} {muMax : Fin p1 → ℝ} {ε : ℕ → ℝ}
    (hpar : Problem.IsParams τ γ ρ1 lamMin lamMax muMax ε)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {ρ : ℕ → ℝ} {lamBar : ℕ → Fin m1 → ℝ}
    {muBar : ℕ → Fin p1 → ℝ} {v : ℕ → Fin m2 → ℝ} {u : ℕ → Fin p2 → ℝ}
    (hrun : P.IsRun τ γ ρ1 lamMin lamMax muMax ε x ρ lamBar muBar v u)
    {xs : EuclideanSpace ℝ (Fin n)} (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : Tendsto (x ∘ φ) atTop (𝓝 xs)) :
    ∃ j₀ : ℕ, ∀ j ≥ j₀,
      (∀ i, P.g1 i xs < 0 → P.muNext x ρ muBar (φ j) i = 0) ∧
        (∀ i, P.g2 i xs < 0 → u (φ j) i = 0) := by
  obtain ⟨hτ0, hτ1, hγ, hρ1, -, -, hε0, hεlim⟩ := hpar
  obtain ⟨-, -, hg1c, -, hg2c⟩ := hP
  set V : ℕ → ℝ := fun k => max ‖(fun i => P.h1 i (x k) : Fin m1 → ℝ)‖ ‖P.sigma x ρ muBar k‖
    with hV
  have hstep : ∀ k, 1 ≤ k → ρ (k + 1) = if V k ≤ τ * V (k - 1) then ρ k else γ * ρ k :=
    fun k hk => (hrun.2.2.2 k hk).2.2.2
  have hρpos : ∀ k, 1 ≤ k → 0 < ρ k := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; rw [hrun.1]; exact hρ1
      · rw [hstep k h0]
        split_ifs
        · exact ih h0
        · exact mul_pos (by linarith) (ih h0)
  have hρmono1 : ∀ k, 1 ≤ k → ρ k ≤ ρ (k + 1) := by
    intro k hk
    rw [hstep k hk]
    split_ifs
    · exact le_rfl
    · have := hρpos k hk; nlinarith
  have hρmono : ∀ a b, 1 ≤ a → a ≤ b → ρ a ≤ ρ b := by
    intro a b ha hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih => exact ih.trans (hρmono1 b (by omega))
  have hmuMax : ∀ k, 1 ≤ k → ∀ i, muBar k i ≤ muMax i := by
    intro k hk i
    rcases Nat.lt_or_ge k 2 with h | h
    · have : k = 1 := by omega
      subst this; exact (hrun.2.2.1 i).2
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact ((hrun.2.2.2 k' (by omega)).2.2.1 i).2
  have hφge : ∀ j, j ≤ φ j := hφ.id_le
  have hφtend : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hev1 : ∀ᶠ j in atTop, 1 ≤ φ j := by
    filter_upwards [eventually_ge_atTop 1] with j hj
    exact hj.trans (hφge j)
  have hg1t : ∀ i, Tendsto (fun j => P.g1 i (x (φ j))) atTop (𝓝 (P.g1 i xs)) := fun i =>
    ((hg1c i).continuous.tendsto xs).comp hconv
  have hg2t : ∀ i, Tendsto (fun j => P.g2 i (x (φ j))) atTop (𝓝 (P.g2 i xs)) := fun i =>
    ((hg2c i).continuous.tendsto xs).comp hconv
  -- g2 part
  have hpart2 : ∀ i, ∀ᶠ j in atTop, P.g2 i xs < 0 → u (φ j) i = 0 := by
    intro i
    by_cases hb : P.g2 i xs < 0
    · have hεφ : Tendsto (fun j => ε (φ j)) atTop (𝓝 0) := hεlim.comp hφtend
      have e1 : ∀ᶠ j in atTop, P.g2 i (x (φ j)) < P.g2 i xs / 2 :=
        (hg2t i).eventually (gt_mem_nhds (by linarith))
      have e2 : ∀ᶠ j in atTop, ε (φ j) < -(P.g2 i xs) / 2 :=
        hεφ.eventually (gt_mem_nhds (by linarith))
      filter_upwards [e1, e2, hev1] with j h1 h2 h3 _
      obtain ⟨ε1, ε2, ε3, -, -, hε2, hε2k, -, -, -, -, hzero, -⟩ := (hrun.2.2.2 (φ j) h3).1
      exact hzero i (by linarith)
    · exact Eventually.of_forall fun j h => absurd h hb
  -- g1 part
  have hpart1 : ∀ i, ∀ᶠ j in atTop, P.g1 i xs < 0 → P.muNext x ρ muBar (φ j) i = 0 := by
    by_cases hevc : ∃ K, 1 ≤ K ∧ ∀ k ≥ K, V k ≤ τ * V (k - 1)
    · obtain ⟨K, hK1, hK⟩ := hevc
      -- ρ is eventually constant
      have hρconst : ∀ m, ρ (K + m) = ρ K := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih =>
          rw [← add_assoc, hstep (K + m) (by omega), if_pos (hK (K + m) (by omega)), ih]
      -- V → 0
      have hVnn : ∀ k, 0 ≤ V k := fun k => le_trans (norm_nonneg _) (le_max_left _ _)
      have hVbound : ∀ m, V (K + m) ≤ τ ^ m * V K := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          have := hK (K + m + 1) (by omega)
          simp only [Nat.add_sub_cancel] at this
          calc V (K + (m + 1)) = V (K + m + 1) := by rw [add_assoc]
            _ ≤ τ * V (K + m) := this
            _ ≤ τ * (τ ^ m * V K) := mul_le_mul_of_nonneg_left ih hτ0
            _ = τ ^ (m + 1) * V K := by ring
      have hVt : Tendsto V atTop (𝓝 0) := by
        rw [← tendsto_add_atTop_iff_nat K]
        have hpow : Tendsto (fun m : ℕ => τ ^ m * V K) atTop (𝓝 0) := by
          have := (tendsto_pow_atTop_nhds_zero_of_lt_one hτ0 hτ1).mul_const (V K)
          simpa using this
        refine squeeze_zero (fun m => hVnn _) (fun m => ?_) hpow
        rw [add_comm]; exact hVbound m
      intro i
      by_cases ha : P.g1 i xs < 0
      · set a := P.g1 i xs
        have hσt : Tendsto (fun j => P.sigma x ρ muBar (φ j) i) atTop (𝓝 0) := by
          refine squeeze_zero_norm (fun j => ?_) (hVt.comp hφtend)
          exact (norm_le_pi_norm (P.sigma x ρ muBar (φ j)) i).trans (le_max_right _ _)
        have e1 : ∀ᶠ j in atTop, P.g1 i (x (φ j)) < a / 2 :=
          (hg1t i).eventually (gt_mem_nhds (by linarith))
        have e2 : ∀ᶠ j in atTop, |P.sigma x ρ muBar (φ j) i| < -a / 2 := by
          have := (hσt.abs).eventually (gt_mem_nhds (show |(0 : ℝ)| < -a / 2 by
            rw [abs_zero]; linarith))
          exact this
        have e3 : ∀ᶠ j in atTop, K ≤ φ j := hφtend.eventually_ge_atTop K
        filter_upwards [e1, e2, e3, hev1] with j h1 h2 h3 h4 _
        have hφ0 : φ j ≠ 0 := by omega
        have hρφ : ρ (φ j) = ρ K := by
          obtain ⟨m, hm⟩ : ∃ m, φ j = K + m := ⟨φ j - K, by omega⟩
          rw [hm, hρconst]
        have hρK : 0 < ρ K := hρpos K hK1
        have hσdef : P.sigma x ρ muBar (φ j) i =
            max (P.g1 i (x (φ j))) (-(muBar (φ j) i) / ρ (φ j)) := by
          simp only [Problem.sigma, if_neg hφ0]
        set σv := P.sigma x ρ muBar (φ j) i
        have hlt : P.g1 i (x (φ j)) < σv := by
          have := neg_abs_le σv
          linarith
        have hb : σv = -(muBar (φ j) i) / ρ (φ j) := by
          rw [hσdef] at hlt ⊢
          rcases le_total (P.g1 i (x (φ j))) (-(muBar (φ j) i) / ρ (φ j)) with h | h
          · exact max_eq_right h
          · rw [max_eq_left h] at hlt; exact absurd hlt (lt_irrefl _)
        have hmu : muBar (φ j) i = -(σv * ρ (φ j)) := by
          rw [hb, hρφ]; field_simp
        have hneg : muBar (φ j) i + ρ (φ j) * P.g1 i (x (φ j)) < 0 := by
          rw [hmu, hρφ]
          have hσ : -σv < -a / 2 := by have := le_abs_self (-σv); rw [abs_neg] at this; linarith
          have : -(σv * ρ K) + ρ K * P.g1 i (x (φ j)) = ρ K * (P.g1 i (x (φ j)) - σv) := by ring
          rw [this]
          apply mul_neg_of_pos_of_neg hρK
          linarith
        simp only [Problem.muNext]
        exact max_eq_left hneg.le
      · exact Eventually.of_forall fun j h => absurd h ha
    · -- infinitely many increases: ρ → ∞
      push_neg at hevc
      have hgrow : ∀ N : ℕ, ∃ k, 1 ≤ k ∧ ρ1 * γ ^ N ≤ ρ k := by
        intro N
        induction N with
        | zero => exact ⟨1, le_rfl, by rw [hrun.1]; simp⟩
        | succ N ih =>
          obtain ⟨k, hk1, hk⟩ := ih
          obtain ⟨k', hk', hfail⟩ := hevc k hk1
          refine ⟨k' + 1, by omega, ?_⟩
          rw [hstep k' (by omega), if_neg (not_le.mpr hfail)]
          have := hρmono k k' hk1 hk'
          rw [pow_succ]
          nlinarith
      have hρtop : Tendsto ρ atTop atTop := by
        rw [tendsto_atTop]
        intro B
        have hpow := tendsto_pow_atTop_atTop_of_one_lt hγ
        obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_atTop.mp hpow) (B / ρ1))
        obtain ⟨k, hk1, hk⟩ := hgrow N
        filter_upwards [eventually_ge_atTop k] with k' hk'
        have h1 := hN N le_rfl
        have h2 : B ≤ ρ1 * γ ^ N := by
          rw [div_le_iff₀ hρ1] at h1; linarith
        linarith [hρmono k k' hk1 hk']
      intro i
      by_cases ha : P.g1 i xs < 0
      · set a := P.g1 i xs
        have e1 : ∀ᶠ j in atTop, P.g1 i (x (φ j)) < a / 2 :=
          (hg1t i).eventually (gt_mem_nhds (by linarith))
        have e2 : ∀ᶠ j in atTop, 2 * (|muMax i| + 1) / (-a) < ρ (φ j) :=
          (hρtop.comp hφtend).eventually (eventually_gt_atTop _)
        filter_upwards [e1, e2, hev1] with j h1 h2 h3 _
        have hρφ := hρpos (φ j) h3
        have hmu := hmuMax (φ j) h3 i
        have hna : 0 < -a := by linarith
        rw [div_lt_iff₀ hna] at h2
        have : ρ (φ j) * P.g1 i (x (φ j)) < ρ (φ j) * (a / 2) :=
          mul_lt_mul_of_pos_left h1 hρφ
        have hneg : muBar (φ j) i + ρ (φ j) * P.g1 i (x (φ j)) < 0 := by
          have := le_abs_self (muMax i)
          nlinarith
        simp only [Problem.muNext]
        exact max_eq_left hneg.le
      · exact Eventually.of_forall fun j h => absurd h ha
  have hall : ∀ᶠ j in atTop, (∀ i, P.g1 i xs < 0 → P.muNext x ρ muBar (φ j) i = 0) ∧
      (∀ i, P.g2 i xs < 0 → u (φ j) i = 0) :=
    (eventually_all.mpr hpart1).and (eventually_all.mpr hpart2)
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hall
  exact ⟨j₀, hj₀⟩
