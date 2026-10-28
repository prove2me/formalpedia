-- Prove2me | solution 1 for AsyncSA.Contraction.lemma3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T19:37:30.074193+00:00
-- url     : https://prove2.me/submissions/9b360774-9490-4c88-a4d4-cd9bc96b8b76

import Mathlib
import Definitions.Def_AsyncSA_Contraction_Model

namespace Aux_ASA_l3

lemma step (x Fv w W α Gc : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hG : 0 < Gc)
    (hl : -Gc + W * Gc ≤ x) (hu : x ≤ Gc + W * Gc) (hF : |Fv| ≤ Gc) :
    -Gc + ((1 - α) * W + α * (w / Gc)) * Gc ≤ x + α * (Fv - x + w) ∧
      x + α * (Fv - x + w) ≤ Gc + ((1 - α) * W + α * (w / Gc)) * Gc := by
  have e : ((1 - α) * W + α * (w / Gc)) * Gc = (1 - α) * W * Gc + α * w := by
    field_simp
  rw [e]
  obtain ⟨h1, h2⟩ := abs_le.mp hF
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr hα1),
      mul_le_mul_of_nonneg_left h1 hα0]
  · nlinarith [mul_le_mul_of_nonneg_left hu (sub_nonneg.mpr hα1),
      mul_le_mul_of_nonneg_left h2 hα0]

lemma absb (x W Gc ε : ℝ) (hG : 0 < Gc) (hW1 : -ε ≤ W) (hW2 : W ≤ ε)
    (hl : -Gc + W * Gc ≤ x) (hu : x ≤ Gc + W * Gc) : |x| ≤ (1 + ε) * Gc := by
  rw [abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right hW1 hG.le,
    mul_le_mul_of_nonneg_right hW2 hG.le]

end Aux_ASA_l3

open AsyncSA.Contraction MeasureTheory Filter Topology Aux_ASA_l3 in
theorem solution {n : ℕ} {Ω : Type*} (alg : Algorithm n Ω) (ω : Ω)
    (γ G₀ ε : ℝ) (G : ℕ → ℝ) (t₀ : ℕ)
    (hγ : 0 ≤ γ ∧ γ < 1) (hG₀ : 0 < G₀) (hε : 0 < ε)
    (hγε : γ * (1 + ε) = 1)
    (hF : ∀ x : Fin n → ℝ, ∀ i,
      |alg.F x i| ≤ γ * max (⨆ j : Fin n, |x j|) G₀)
    (hGinit : G 0 = max (alg.runMax 0 ω) G₀)
    (hGstay : ∀ t, alg.runMax (t + 1) ω ≤ (1 + ε) * G t → G (t + 1) = G t)
    (hGjump : ∀ t, (1 + ε) * G t < alg.runMax (t + 1) ω →
      ∃ k : ℕ, G (t + 1) = G₀ * (1 + ε) ^ k ∧
        G₀ * (1 + ε) ^ (k - 1) < alg.runMax (t + 1) ω ∧
        alg.runMax (t + 1) ω ≤ G₀ * (1 + ε) ^ k)
    (hM₀ : alg.runMax t₀ ω ≤ G t₀)
    (hW : ∀ t ≥ t₀, ∀ i : Fin n,
      |tailW (fun s => alg.α i s ω)
        (fun s => alg.w i s ω / G s) t₀ t| ≤ ε)
    (hunbounded : ¬ ∃ M : ℝ, ∀ t j, |alg.x t ω j| ≤ M) :
    ∀ t ≥ t₀, G t = G t₀ ∧ ∀ i : Fin n,
      let W := tailW (fun s => alg.α i s ω)
        (fun s => alg.w i s ω / G s) t₀ t;
      -(G t₀ * (1 + ε)) ≤ -G t₀ + W * G t₀ ∧
        -G t₀ + W * G t₀ ≤ alg.x t ω i ∧
        alg.x t ω i ≤ G t₀ + W * G t₀ ∧
        G t₀ + W * G t₀ ≤ G t₀ * (1 + ε) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, alg.n_pos⟩⟩
  -- G is always at least G₀
  have hGge : ∀ t, G₀ ≤ G t := by
    intro t
    induction t with
    | zero => rw [hGinit]; exact le_max_right _ _
    | succ k ih =>
      by_cases h : alg.runMax (k + 1) ω ≤ (1 + ε) * G k
      · rw [hGstay k h]; exact ih
      · obtain ⟨m, hm, -, -⟩ := hGjump k (lt_of_not_ge h)
        rw [hm]
        exact le_mul_of_one_le_right hG₀.le (one_le_pow₀ (by linarith))
  obtain ⟨Gc, hGcd⟩ : ∃ Gc, Gc = G t₀ := ⟨_, rfl⟩
  rw [← hGcd] at hM₀ ⊢
  have hGc0 : 0 < Gc := lt_of_lt_of_le hG₀ (hGcd ▸ hGge t₀)
  have hG₀c : G₀ ≤ Gc := hGcd ▸ hGge t₀
  -- abbreviations
  let W : Fin n → ℕ → ℝ := fun i t =>
    tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω / G s) t₀ t
  have hWb : ∀ t ≥ t₀, ∀ i, -ε ≤ W i t ∧ W i t ≤ ε := fun t ht i => abs_le.mp (hW t ht i)
  have hW0 : ∀ i, W i t₀ = 0 := by
    intro i
    simp only [W]
    cases t₀ with
    | zero => rfl
    | succ k => simp [tailW]
  have hWs : ∀ i t, t₀ ≤ t → W i (t + 1) =
      (1 - alg.α i t ω) * W i t + alg.α i t ω * (alg.w i t ω / G t) := by
    intro i t ht
    simp only [W]
    rw [tailW, if_pos ht]
  -- values before t₀ bounded by runMax t₀
  have hpre : ∀ s, s ≤ t₀ → ∀ j, |alg.x s ω j| ≤ Gc := by
    intro s hs j
    refine le_trans ?_ hM₀
    have h1 : |alg.x s ω j| ≤ ⨆ j : Fin n, |alg.x s ω j| :=
      le_ciSup (f := fun j : Fin n => |alg.x s ω j|) (Finite.bddAbove_range _) j
    refine le_trans h1 ?_
    unfold Algorithm.runMax
    exact le_ciSup (f := fun s : Fin (t₀ + 1) => ⨆ j : Fin n, |alg.x (s : ℕ) ω j|)
      (Finite.bddAbove_range _) ⟨s, by omega⟩
  let Q : ℕ → Prop := fun s => G s = Gc ∧ ∀ i, -Gc + W i s * Gc ≤ alg.x s ω i ∧
    alg.x s ω i ≤ Gc + W i s * Gc
  have hQabs : ∀ s, t₀ ≤ s → Q s → ∀ j, |alg.x s ω j| ≤ (1 + ε) * Gc := by
    intro s hs hQ j
    obtain ⟨h1, h2⟩ := hWb s hs j
    exact absb _ _ _ _ hGc0 h1 h2 (hQ.2 j).1 (hQ.2 j).2
  have hall : ∀ s, s ≤ t₀ ∨ t₀ ≤ s := fun s => le_total s t₀
  have R : ∀ t, t₀ ≤ t → ∀ s, t₀ ≤ s → s ≤ t → Q s := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
      intro s hs1 hs2
      have : s = t₀ := le_antisymm hs2 hs1
      subst this
      refine ⟨hGcd.symm, fun i => ?_⟩
      rw [hW0 i, zero_mul, add_zero, add_zero]
      exact abs_le.mp (hpre s le_rfl i)
    | succ t ht ih =>
      -- bound for all s ≤ t
      have hb : ∀ s, s ≤ t → ∀ j, |alg.x s ω j| ≤ (1 + ε) * Gc := by
        intro s hs j
        rcases hall s with h | h
        · exact le_trans (hpre s h j) (by nlinarith)
        · exact hQabs s h (ih s h hs) j
      have hGt : G t = Gc := (ih t ht le_rfl).1
      have hnew : ∀ i, -Gc + W i (t + 1) * Gc ≤ alg.x (t + 1) ω i ∧
          alg.x (t + 1) ω i ≤ Gc + W i (t + 1) * Gc := by
        intro i
        have hFb : |alg.F (fun j => alg.x (alg.τ i j t ω) ω j) i| ≤ Gc := by
          refine le_trans (hF _ i) ?_
          have hsup : (⨆ j : Fin n, |alg.x (alg.τ i j t ω) ω j|) ≤ (1 + ε) * Gc :=
            ciSup_le fun j => hb _ (alg.τ_le i j t ω) j
          have hmax : max (⨆ j : Fin n, |alg.x (alg.τ i j t ω) ω j|) G₀ ≤ (1 + ε) * Gc :=
            max_le hsup (by nlinarith)
          calc γ * max (⨆ j : Fin n, |alg.x (alg.τ i j t ω) ω j|) G₀
              ≤ γ * ((1 + ε) * Gc) := mul_le_mul_of_nonneg_left hmax hγ.1
            _ = Gc := by rw [← mul_assoc, hγε, one_mul]
        rw [alg.update i t ω, hWs i t ht, hGt]
        obtain ⟨hα0, hα1⟩ := alg.α_mem i t ω
        obtain ⟨hl, hu⟩ := (ih t ht le_rfl).2 i
        exact step _ _ _ _ _ _ hα0 hα1 hGc0 hl hu hFb
      have hrun : alg.runMax (t + 1) ω ≤ (1 + ε) * G t := by
        rw [hGt]
        unfold Algorithm.runMax
        refine ciSup_le fun s => ciSup_le fun j => ?_
        have hs := s.isLt
        rcases Nat.lt_or_ge (s : ℕ) (t + 1) with h | h
        · exact hb s (by omega) j
        · have : (s : ℕ) = t + 1 := by omega
          rw [this]
          obtain ⟨h1, h2⟩ := hWb (t + 1) (by omega) j
          exact absb _ _ _ _ hGc0 h1 h2 (hnew j).1 (hnew j).2
      have hQ1 : Q (t + 1) := ⟨by rw [hGstay t hrun, hGt], hnew⟩
      intro s hs1 hs2
      rcases Nat.lt_or_ge s (t + 1) with h | h
      · exact ih s hs1 (by omega)
      · have : s = t + 1 := by omega
        subst this; exact hQ1
  intro t ht
  obtain ⟨hGt, hx⟩ := R t ht t ht le_rfl
  refine ⟨hGt, fun i => ?_⟩
  obtain ⟨h1, h2⟩ := hWb t ht i
  obtain ⟨hl, hu⟩ := hx i
  refine ⟨?_, hl, hu, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right h1 hGc0.le]
  · nlinarith [mul_le_mul_of_nonneg_right h2 hGc0.le]
