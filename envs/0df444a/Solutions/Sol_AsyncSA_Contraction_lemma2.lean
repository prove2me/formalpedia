-- Prove2me | solution 1 for AsyncSA.Contraction.lemma2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T11:20:38.102457+00:00
-- url     : https://prove2.me/submissions/ce64993c-f787-4169-96f4-44ebdd92003f

import Mathlib
import Definitions.Def_AsyncSA_Contraction_Model
import Theorems.Thm_AsyncSA_Contraction_lemma1

open MeasureTheory Filter Topology
open AsyncSA.Contraction

namespace AsyncSA.Contraction.Lem2Aux

lemma tailW_self (a b : ℕ → ℝ) (t₀ : ℕ) : tailW a b t₀ t₀ = 0 := by
  cases t₀ with
  | zero => rfl
  | succ s => simp [tailW]

lemma tailW_diff (a b : ℕ → ℝ) (ha : ∀ t, a t ∈ Set.Icc (0:ℝ) 1) (t₀ k : ℕ) :
    |tailW a b 0 (t₀ + k) - tailW a b t₀ (t₀ + k)| ≤ |tailW a b 0 t₀| := by
  induction k with
  | zero => simp [tailW_self]
  | succ k ih =>
    rw [← add_assoc]
    simp only [tailW, if_pos (Nat.zero_le (t₀ + k)), if_pos (Nat.le_add_right t₀ k)]
    have e : (1 - a (t₀ + k)) * tailW a b 0 (t₀ + k) + a (t₀ + k) * b (t₀ + k) -
        ((1 - a (t₀ + k)) * tailW a b t₀ (t₀ + k) + a (t₀ + k) * b (t₀ + k)) =
        (1 - a (t₀ + k)) * (tailW a b 0 (t₀ + k) - tailW a b t₀ (t₀ + k)) := by ring
    rw [e, abs_mul, abs_of_nonneg (by linarith [(ha (t₀ + k)).2])]
    have h0 : 0 ≤ 1 - a (t₀ + k) := by linarith [(ha (t₀ + k)).2]
    have h1 : 1 - a (t₀ + k) ≤ 1 := by linarith [(ha (t₀ + k)).1]
    calc (1 - a (t₀ + k)) * |tailW a b 0 (t₀ + k) - tailW a b t₀ (t₀ + k)|
        ≤ 1 * |tailW a b 0 (t₀ + k) - tailW a b t₀ (t₀ + k)| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact ih

end AsyncSA.Contraction.Lem2Aux

open AsyncSA.Contraction.Lem2Aux in
theorem solution {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ m₀) (α w B : ℕ → Ω → ℝ) (C : ℝ)
    (hαmeas : ∀ t, Measurable[𝓕 t] (α t))
    (hwmeas : ∀ t, Measurable[𝓕 (t + 1)] (w t))
    (hBmeas : ∀ t, Measurable[𝓕 t] (B t))
    (hmean : ∀ t, CondMeanZero m₀ (𝓕 t) P (w t))
    (hsq : ∀ t, CondSqLe m₀ (𝓕 t) P (w t) (B t))
    (hαmem : ∀ᵐ ω ∂P, ∀ t, α t ω ∈ Set.Icc (0 : ℝ) 1)
    (hdiv : ∀ᵐ ω ∂P,
      Tendsto (fun T => ∑ t ∈ Finset.range T, α t ω) atTop atTop)
    (hsum : ∀ᵐ ω ∂P,
      ∀ T, ∑ t ∈ Finset.range T, α t ω ^ 2 ≤ C)
    (hBbound : ∀ᵐ ω ∂P, ∃ K : ℝ, ∀ t, |B t ω| ≤ K) :
    ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
      ∃ T : ℕ, ∀ t₀ t : ℕ, T ≤ t₀ → t₀ ≤ t →
        |tailW (fun s => α s ω) (fun s => w s ω) t₀ t| ≤ δ := by
  have hW : ∀ t ω, tailW (fun s => α s ω) (fun s => w s ω) 0 (t + 1) =
      (1 - α t ω) * tailW (fun s => α s ω) (fun s => w s ω) 0 t + α t ω * w t ω := by
    intro t ω; simp [tailW]
  have hconv := lemma1 P 𝓕 α w B (fun t ω => tailW (fun s => α s ω) (fun s => w s ω) 0 t) C
    hαmeas hwmeas hBmeas hmean hsq hαmem hdiv hsum hBbound hW
  filter_upwards [hconv, hαmem] with ω hω hα
  intro δ hδ
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.1 hω) (δ / 2) (by positivity)
  refine ⟨T, fun t₀ t ht₀ ht => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  have hd := tailW_diff (fun s => α s ω) (fun s => w s ω) hα t₀ k
  have h1 := hT (t₀ + k) (by omega)
  have h2 := hT t₀ ht₀
  simp only [Real.dist_eq, sub_zero] at h1 h2
  set A := tailW (fun s => α s ω) (fun s => w s ω) 0 (t₀ + k)
  set A0 := tailW (fun s => α s ω) (fun s => w s ω) 0 t₀
  set X := tailW (fun s => α s ω) (fun s => w s ω) t₀ (t₀ + k)
  have h1' : |A| < δ / 2 := h1
  have h2' : |A0| < δ / 2 := h2
  obtain ⟨hd1, hd2⟩ := abs_le.1 hd
  obtain ⟨h11, h12⟩ := abs_lt.1 h1'
  rw [abs_le]
  constructor <;> linarith
