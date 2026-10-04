-- Prove2me | solution 1 for AppliedComb.InclExcl.surjections_count
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T18:02:22.662042+00:00
-- url     : https://prove2.me/submissions/5b2aebba-99ae-42bd-96f5-82ef5a50bdd5

import Mathlib

open Finset in
theorem surjCount_aux_card (n m : ℕ) (t : Finset (Fin m)) :
    #((Finset.univ : Finset (Fin n → Fin m)).filter (fun f => ∀ j, f j ∉ t)) = (m - #t) ^ n := by
  have h : (Finset.univ : Finset (Fin n → Fin m)).filter (fun f => ∀ j, f j ∉ t)
      = Fintype.piFinset (fun _ : Fin n => tᶜ) := by
    ext f; simp [Fintype.mem_piFinset]
  rw [h, Fintype.card_piFinset]
  simp [Finset.card_compl]

open Finset in
theorem solution (n m : ℕ) :
    (Fintype.card {f : Fin n → Fin m // Function.Surjective f} : ℤ) =
      ∑ k ∈ Finset.range (m + 1),
        (-1 : ℤ) ^ k * (m.choose k : ℤ) * ((m - k : ℕ) : ℤ) ^ n := by
  classical
  let S : Fin m → Finset (Fin n → Fin m) := fun i => Finset.univ.filter (fun f => ∀ j, f j ≠ i)
  have h1 : Fintype.card {f : Fin n → Fin m // Function.Surjective f}
      = #((Finset.univ : Finset (Fin m)).inf fun i => (S i)ᶜ) := by
    refine Fintype.card_of_subtype _ (fun f => ?_)
    simp [S, Finset.mem_inf, Function.Surjective]
  have h2 : ∀ t : Finset (Fin m), #(t.inf S) = (m - #t) ^ n := by
    intro t
    rw [← surjCount_aux_card n m t]
    congr 1
    ext f
    simp only [Finset.mem_inf, S, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h j hj; exact h _ hj j rfl
    · intro h i hi j hj; exact h j (hj ▸ hi)
  rw [h1, Finset.inclusion_exclusion_card_inf_compl]
  simp_rw [h2]
  have h3 := Finset.sum_powerset_apply_card
    (fun k : ℕ => (-1 : ℤ) ^ k * (((m - k : ℕ) : ℤ)) ^ n) (x := (Finset.univ : Finset (Fin m)))
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
  push_cast at h3 ⊢
  rw [h3]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring
