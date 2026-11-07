-- Prove2me | solution 1 for AsyncSA.Monotone.lemma5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T11:42:34.303858+00:00
-- url     : https://prove2.me/submissions/bc5474f1-d58a-48cf-ad4d-76805c4f89f5

import Mathlib
import Definitions.Def_AsyncSA_Monotone_Model

open AsyncSA.Monotone Filter Topology

theorem solution {n : ℕ} (F : (Fin n → ℝ) → Fin n → ℝ) (xstar : Fin n → ℝ) (r : ℝ)
    (h4 : Assumption4 F xstar) (hr : 0 < r) :
    Tendsto (Useq F xstar r) atTop (𝓝 xstar) ∧ Tendsto (Lseq F xstar r) atTop (𝓝 xstar) := by
  have h1 : (0 : Fin n → ℝ) ≤ r • (1 : Fin n → ℝ) := fun j => by simp [hr.le]
  -- upper sequence: F(U^k) ≤ U^k, x* ≤ U^k
  have hUF : ∀ k, F (Useq F xstar r k) ≤ Useq F xstar r k ∧ xstar ≤ Useq F xstar r k := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · have := (h4.shift xstar r hr).2.2
        rw [h4.fixed] at this
        simpa [Useq] using this
      · intro j; simp [Useq, hr.le]
    | succ k ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hle : Useq F xstar r (k + 1) ≤ Useq F xstar r k := by
        intro j; have := ih1 j; simp only [Useq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; linarith
      have hge : F (Useq F xstar r k) ≤ Useq F xstar r (k + 1) := by
        intro j; have := ih1 j; simp only [Useq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; linarith
      refine ⟨le_trans (h4.mono hle) hge, ?_⟩
      have hF : xstar ≤ F (Useq F xstar r k) := by
        have := h4.mono ih2; rwa [h4.fixed] at this
      intro j; have := ih2 j; have := hF j
      simp only [Useq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; linarith
  have hLF : ∀ k, Lseq F xstar r k ≤ F (Lseq F xstar r k) ∧ Lseq F xstar r k ≤ xstar := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · have := (h4.shift xstar r hr).1
        rw [h4.fixed] at this
        simpa [Lseq] using this
      · intro j; simp [Lseq, hr.le]
    | succ k ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hle : Lseq F xstar r k ≤ Lseq F xstar r (k + 1) := by
        intro j; have := ih1 j; simp only [Lseq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; linarith
      have hge : Lseq F xstar r (k + 1) ≤ F (Lseq F xstar r k) := by
        intro j; have := ih1 j; simp only [Lseq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; linarith
      refine ⟨le_trans hge (h4.mono hle), ?_⟩
      have hF : F (Lseq F xstar r k) ≤ xstar := by
        have := h4.mono ih2; rwa [h4.fixed] at this
      intro j; have := ih2 j; have := hF j
      simp only [Lseq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; linarith
  have hUanti : ∀ j, Antitone (fun k => Useq F xstar r k j) := by
    intro j
    refine antitone_nat_of_succ_le fun k => ?_
    have := (hUF k).1 j
    simp only [Useq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; linarith
  have hLmono : ∀ j, Monotone (fun k => Lseq F xstar r k j) := by
    intro j
    refine monotone_nat_of_le_succ fun k => ?_
    have := (hLF k).1 j
    simp only [Lseq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; linarith
  -- limits
  have key : ∀ (S : ℕ → Fin n → ℝ) (u : Fin n → ℝ), Tendsto S atTop (𝓝 u) →
      (∀ k, S (k + 1) = (1 / 2 : ℝ) • (S k + F (S k))) → u = xstar := by
    intro S u hS hrec
    have hA : Tendsto (fun k => S (k + 1)) atTop (𝓝 u) := hS.comp (tendsto_add_atTop_nat 1)
    have hB : Tendsto (fun k => (1 / 2 : ℝ) • (S k + F (S k))) atTop
        (𝓝 ((1 / 2 : ℝ) • (u + F u))) :=
      (hS.add ((h4.cont.tendsto u).comp hS)).const_smul _
    have hAB : (fun k => S (k + 1)) = (fun k => (1 / 2 : ℝ) • (S k + F (S k))) := funext hrec
    rw [hAB] at hA
    have he := tendsto_nhds_unique hA hB
    apply h4.unique
    funext j
    have := congrFun he j
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this
    linarith
  refine ⟨?_, ?_⟩
  · set u : Fin n → ℝ := fun j => ⨅ k, Useq F xstar r k j
    have hU : Tendsto (Useq F xstar r) atTop (𝓝 u) := by
      rw [tendsto_pi_nhds]
      intro j
      exact tendsto_atTop_ciInf (hUanti j) ⟨xstar j, by
        rintro _ ⟨k, rfl⟩; exact (hUF k).2 j⟩
    have := key _ u hU (fun k => rfl)
    rwa [this] at hU
  · set u : Fin n → ℝ := fun j => ⨆ k, Lseq F xstar r k j
    have hL : Tendsto (Lseq F xstar r) atTop (𝓝 u) := by
      rw [tendsto_pi_nhds]
      intro j
      exact tendsto_atTop_ciSup (hLmono j) ⟨xstar j, by
        rintro _ ⟨k, rfl⟩; exact (hLF k).2 j⟩
    have := key _ u hL (fun k => rfl)
    rwa [this] at hL
