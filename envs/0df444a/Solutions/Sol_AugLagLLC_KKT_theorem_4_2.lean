-- Prove2me | solution 1 for AugLagLLC.KKT.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T16:32:17.070164+00:00
-- url     : https://prove2.me/submissions/b4046b88-dc5d-4a4e-941a-4535cf06d84d

import Mathlib
import Definitions.Def_AugLagLLC_KKT_Setting
import Theorems.Thm_AugLagLLC_KKT_eq_4_9
import Theorems.Thm_AugLagLLC_KKT_eq_4_10
import Theorems.Thm_AugLagLLC_KKT_cpld_limit_kkt
import Theorems.Thm_AugLagLLC_KKT_mfcq_multipliers_bounded

open Filter Topology
open AugLagLLC.KKT

theorem solution {n m1 p1 m2 p2 : ℕ} (P : Problem n m1 p1 m2 p2) (hP : P.IsC1)
    {τ γ ρ1 : ℝ} {lamMin lamMax : Fin m1 → ℝ} {muMax : Fin p1 → ℝ} {ε : ℕ → ℝ}
    (hpar : Problem.IsParams τ γ ρ1 lamMin lamMax muMax ε)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {ρ : ℕ → ℝ} {lamBar : ℕ → Fin m1 → ℝ}
    {muBar : ℕ → Fin p1 → ℝ} {v : ℕ → Fin m2 → ℝ} {u : ℕ → Fin p2 → ℝ}
    (hrun : P.IsRun τ γ ρ1 lamMin lamMax muMax ε x ρ lamBar muBar v u)
    {xs : EuclideanSpace ℝ (Fin n)} (hlim : MapClusterPt xs atTop x)
    (hfeas : xs ∈ P.Omega1 ∩ P.Omega2)
    (hcpld : CPLDAt (Sum.elim P.h1 P.h2) (Sum.elim P.g1 P.g2) xs) :
    IsKKT P.f (Sum.elim P.h1 P.h2) (Sum.elim P.g1 P.g2) xs ∧
      (MFCQAt (Sum.elim P.h1 P.h2) (Sum.elim P.g1 P.g2) xs →
        ∀ φ : ℕ → ℕ, StrictMono φ → Tendsto (x ∘ φ) atTop (𝓝 xs) →
          ∃ C : ℝ, ∀ j, ‖P.lamNext x ρ lamBar (φ j)‖ ≤ C ∧ ‖P.muNext x ρ muBar (φ j)‖ ≤ C ∧
            ‖v (φ j)‖ ≤ C ∧ ‖u (φ j)‖ ≤ C) := by
  obtain ⟨hf, hh1, hg1, hh2, hg2⟩ := hP
  have hFc : ContDiff ℝ 1 P.f := hf
  have hHc : ∀ i, ContDiff ℝ 1 (Sum.elim P.h1 P.h2 i) := by
    rintro (i | i) <;> simp [hh1, hh2]
  have hGc : ∀ j, ContDiff ℝ 1 (Sum.elim P.g1 P.g2 j) := by
    rintro (i | i) <;> simp [hg1, hg2]
  obtain ⟨⟨hfeas1, hfeas2⟩, hfeas3, hfeas4⟩ := hfeas
  have hHx : ∀ i, Sum.elim P.h1 P.h2 i xs = 0 := by
    rintro (i | i) <;> simp [hfeas1, hfeas3]
  have hGx : ∀ j, Sum.elim P.g1 P.g2 j xs ≤ 0 := by
    rintro (i | i) <;> simp [hfeas2, hfeas4]
  -- the shifted subsequence and its multipliers
  have key : ∀ φ : ℕ → ℕ, StrictMono φ → Tendsto (x ∘ φ) atTop (𝓝 xs) →
      ∃ N : ℕ, ∃ (a : ℕ → Fin m1 ⊕ Fin m2 → ℝ) (b : ℕ → Fin p1 ⊕ Fin p2 → ℝ),
        Tendsto (fun j => x (φ (j + N))) atTop (𝓝 xs) ∧
        (∀ j, a j = Sum.elim (P.lamNext x ρ lamBar (φ (j + N))) (v (φ (j + N)))) ∧
        (∀ j, b j = Sum.elim (P.muNext x ρ muBar (φ (j + N))) (u (φ (j + N)))) ∧
        (∀ k j, 0 ≤ b k j) ∧ (∀ k j, Sum.elim P.g1 P.g2 j xs < 0 → b k j = 0) ∧
        Tendsto (fun k => gradient P.f (x (φ (k + N)))
          + ∑ i, a k i • gradient (Sum.elim P.h1 P.h2 i) (x (φ (k + N)))
          + ∑ j, b k j • gradient (Sum.elim P.g1 P.g2 j) (x (φ (k + N)))) atTop (𝓝 0) := by
    intro φ hφ hconv
    obtain ⟨j₀, hj₀⟩ := eq_4_10 P ⟨hf, hh1, hg1, hh2, hg2⟩ hpar hrun φ hφ hconv
    have hshift : Tendsto (fun j => j + (j₀ + 1)) atTop atTop := tendsto_add_atTop_nat _
    have hφt : Tendsto (fun j => φ (j + (j₀ + 1))) atTop atTop :=
      hφ.tendsto_atTop.comp hshift
    have hge : ∀ j, 1 ≤ φ (j + (j₀ + 1)) := fun j => le_trans (show 1 ≤ j + (j₀ + 1) by omega) (hφ.id_le _)
    refine ⟨j₀ + 1, fun j => Sum.elim (P.lamNext x ρ lamBar (φ (j + (j₀ + 1))))
      (v (φ (j + (j₀ + 1)))), fun j => Sum.elim (P.muNext x ρ muBar (φ (j + (j₀ + 1))))
      (u (φ (j + (j₀ + 1)))), ?_, fun _ => rfl, fun _ => rfl, ?_, ?_, ?_⟩
    · exact hconv.comp hshift
    · intro k j
      obtain ⟨_, hu, hmu⟩ := eq_4_9 P ⟨hf, hh1, hg1, hh2, hg2⟩ hpar hrun _ (hge k)
      rcases j with j | j
      · exact hmu j
      · exact hu j
    · intro k j hj
      obtain ⟨h1, h2⟩ := hj₀ (k + (j₀ + 1)) (by omega)
      rcases j with j | j
      · exact h1 j hj
      · exact h2 j hj
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      have hε : Tendsto (fun k => ε (φ (k + (j₀ + 1)))) atTop (𝓝 0) :=
        hpar.2.2.2.2.2.2.2.comp hφt
      refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hε
      have := (eq_4_9 P ⟨hf, hh1, hg1, hh2, hg2⟩ hpar hrun _ (hge k)).1
      refine le_trans (le_of_eq (congrArg _ ?_)) this
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      abel
  refine ⟨?_, ?_⟩
  · obtain ⟨φ, hφ, hconv⟩ := hlim.tendsto_subseq
    obtain ⟨N, a, b, hy, -, -, hb, hbG, hres⟩ := key φ hφ hconv
    exact cpld_limit_kkt hFc hHc hGc hHx hGx hcpld hy a b hb hbG hres
  · intro hmfcq φ hφ hconv
    obtain ⟨N, a, b, hy, ha, hb', hb, hbG, hres⟩ := key φ hφ hconv
    obtain ⟨C, hC⟩ := mfcq_multipliers_bounded hFc hHc hGc hHx hGx hmfcq hy a b hb hbG hres
    set S : ℝ := ∑ i ∈ Finset.range N, (‖P.lamNext x ρ lamBar (φ i)‖ +
      ‖P.muNext x ρ muBar (φ i)‖ + ‖v (φ i)‖ + ‖u (φ i)‖) with hS
    refine ⟨max C S, fun j => ?_⟩
    by_cases hj : j < N
    · have hle : ‖P.lamNext x ρ lamBar (φ j)‖ + ‖P.muNext x ρ muBar (φ j)‖ + ‖v (φ j)‖ +
          ‖u (φ j)‖ ≤ S :=
        Finset.single_le_sum (f := fun i => ‖P.lamNext x ρ lamBar (φ i)‖ +
          ‖P.muNext x ρ muBar (φ i)‖ + ‖v (φ i)‖ + ‖u (φ i)‖)
          (fun i _ => by positivity) (Finset.mem_range.2 hj)
      have h1 := norm_nonneg (P.lamNext x ρ lamBar (φ j))
      have h2 := norm_nonneg (P.muNext x ρ muBar (φ j))
      have h3 := norm_nonneg (v (φ j))
      have h4 := norm_nonneg (u (φ j))
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        exact le_trans (by linarith) (le_max_right C S)
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + N := ⟨j - N, by omega⟩
      obtain ⟨hCa, hCb⟩ := hC k
      rw [ha k] at hCa
      rw [hb' k] at hCb
      have e1 : ∀ i, ‖P.lamNext x ρ lamBar (φ (k + N)) i‖ ≤ C := fun i =>
        le_trans (by simpa using norm_le_pi_norm (Sum.elim (P.lamNext x ρ lamBar (φ (k + N)))
          (v (φ (k + N)))) (Sum.inl i)) hCa
      have e2 : ∀ i, ‖v (φ (k + N)) i‖ ≤ C := fun i =>
        le_trans (by simpa using norm_le_pi_norm (Sum.elim (P.lamNext x ρ lamBar (φ (k + N)))
          (v (φ (k + N)))) (Sum.inr i)) hCa
      have e3 : ∀ i, ‖P.muNext x ρ muBar (φ (k + N)) i‖ ≤ C := fun i =>
        le_trans (by simpa using norm_le_pi_norm (Sum.elim (P.muNext x ρ muBar (φ (k + N)))
          (u (φ (k + N)))) (Sum.inl i)) hCb
      have e4 : ∀ i, ‖u (φ (k + N)) i‖ ≤ C := fun i =>
        le_trans (by simpa using norm_le_pi_norm (Sum.elim (P.muNext x ρ muBar (φ (k + N)))
          (u (φ (k + N)))) (Sum.inr i)) hCb
      have hC0 : 0 ≤ C := le_trans (norm_nonneg _) hCa
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact le_trans ((pi_norm_le_iff_of_nonneg hC0).2 e1) (le_max_left _ _)
      · exact le_trans ((pi_norm_le_iff_of_nonneg hC0).2 e3) (le_max_left _ _)
      · exact le_trans ((pi_norm_le_iff_of_nonneg hC0).2 e2) (le_max_left _ _)
      · exact le_trans ((pi_norm_le_iff_of_nonneg hC0).2 e4) (le_max_left _ _)
