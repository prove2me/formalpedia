-- Prove2me | solution 1 for AlgMechDesign.Randomized.weighted_vgc_truthful
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:10:47.907273+00:00
-- url     : https://prove2.me/submissions/d7991794-a4aa-4d48-bbec-9ed82ecfdb0f

import Definitions.Def_AlgMechDesign_Randomized_WeightedVGC

set_option autoImplicit false
open AlgMechDesign.Randomized
open Finset

theorem solution {n : ℕ} {O : Type*} {T : Fin n → Type*}
    (v : ∀ i, T i → O → ℝ) (β : Fin n → ℝ) (hβ : ∀ i, 0 < β i)
    (o : (∀ i, T i) → O) (p : (∀ i, T i) → Fin n → ℝ) (hvgc : IsWeightedVGC v β o p) :
    IsTruthfulGeneral v o p := by
  rcases hvgc with ⟨ho, h, hh, hpay⟩
  intro t i ti'
  let u := Function.update t i ti'
  have hh' : h i u = h i t := by
    apply hh
    intro j hj
    simp [u, hj]
  have hs : (∑ j ∈ univ.erase i, β j * v j (u j) (o u)) =
      ∑ j ∈ univ.erase i, β j * v j (t j) (o u) := by
    apply sum_congr rfl
    intro j hj
    simp [u, (mem_erase.mp hj).1]
  have hm := ho t (o u)
  have hm' : (∑ j ∈ univ.erase i, β j * v j (t j) (o u)) + β i * v i (t i) (o u) ≤
      (∑ j ∈ univ.erase i, β j * v j (t j) (o t)) + β i * v i (t i) (o t) := by
    simpa only [sum_erase_add _ _ (mem_univ i)] using hm
  change v i (t i) (o u) + p u i ≤ v i (t i) (o t) + p t i
  rw [hpay u i, hpay t i, hh', hs]
  apply (mul_le_mul_iff_right₀ (hβ i)).mp
  have hcancel : β i * (1 / β i) = 1 := by field_simp [(hβ i).ne']
  simp only [mul_add, ← mul_assoc, hcancel, one_mul]
  linarith

