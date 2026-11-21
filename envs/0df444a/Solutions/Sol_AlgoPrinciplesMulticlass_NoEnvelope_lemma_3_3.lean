-- Prove2me | solution 1 for AlgoPrinciplesMulticlass.NoEnvelope.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T09:52:59.267573+00:00
-- url     : https://prove2.me/submissions/cc407918-96f3-4c54-860d-67bab3bfe64c

import Mathlib
import Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_Construction

section
namespace AlgoPrinciplesMulticlass
open NoEnvelope

theorem chk_lemma_3_3 (F : Set (Pt → Label)) (d : ℕ) (hd : 1 ≤ d) :
    Condition1 F d ∨ Condition2 F d := by
  by_cases h1 : Condition1 F d
  · exact Or.inl h1
  right
  have hg : ∀ v : List (Fin d → Bool), ∃ c : Fin d → Bool, ¬ RealizesOnBlock F d v c := by
    intro v
    by_contra hcon
    push_neg at hcon
    exact h1 ⟨v, hcon⟩
  choose g hg using hg
  let L : ℕ → List (Fin d → Bool) := fun n => Nat.rec [] (fun _ l => l ++ [g l]) n
  have hL : ∀ n, L (n + 1) = L n ++ [g (L n)] := fun n => rfl
  have hlen : ∀ n, (L n).length = n := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [hL]; simp [ih]
  refine ⟨fun i => g (L i), fun i => ?_⟩
  have : List.ofFn (fun k : Fin i => g (L k)) = L i := by
    induction i with
    | zero => rfl
    | succ n ih => 
      rw [List.ofFn_succ']
      simp only [Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]
      rw [hL]
      congr 1
      simpa using ih
  rw [this]
  exact hg _

end AlgoPrinciplesMulticlass
end

theorem solution : type_of% @AlgoPrinciplesMulticlass.chk_lemma_3_3 := @AlgoPrinciplesMulticlass.chk_lemma_3_3
