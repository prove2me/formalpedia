-- Prove2me | solution 1 for AaronsonAmbainis.Row.hasDegreeLE_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:19:42.261241+00:00
-- url     : https://prove2.me/submissions/333af468-8b62-4518-a8a9-29a080076307

import Definitions.Def_AaronsonAmbainis_Row_Chi
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_congr
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_chi
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_zero
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_const_mul
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_sum
import Theorems.Thm_AaronsonAmbainis_Row_chi_mul_chi


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {β : Type*} [Fintype β]
namespace AaronsonAmbainis.Row
theorem _root_.solution {f g : Cube β → ℝ} {k l : ℕ} (hf : HasDegreeLE f k)
    (hg : HasDegreeLE g l) : HasDegreeLE (fun w => f w * g w) (k + l) := by
  classical
  obtain ⟨c, hc, hf⟩ := hf
  obtain ⟨c', hc', hg⟩ := hg
  have key : HasDegreeLE (fun w => ∑ S ∈ (univ : Finset (Finset β)),
      ∑ T ∈ (univ : Finset (Finset β)), c S * c' T * chi (symmDiff S T) w) (k + l) := by
    apply hasDegreeLE_sum
    intro S _
    apply hasDegreeLE_sum
    intro T _
    by_cases hST : S.card ≤ k ∧ T.card ≤ l
    · refine hasDegreeLE_const_mul _ (hasDegreeLE_chi _ ?_)
      have hsub : symmDiff S T ⊆ S ∪ T := by
        intro i hi
        rw [Finset.mem_symmDiff] at hi
        rw [Finset.mem_union]
        tauto
      calc (symmDiff S T).card ≤ (S ∪ T).card := Finset.card_le_card hsub
        _ ≤ S.card + T.card := Finset.card_union_le S T
        _ ≤ k + l := Nat.add_le_add hST.1 hST.2
    · have h0 : c S * c' T = 0 := by
        rcases not_and_or.mp hST with h | h
        · rw [hc S (not_le.mp h), zero_mul]
        · rw [hc' T (not_le.mp h), mul_zero]
      exact hasDegreeLE_congr (hasDegreeLE_zero _) (fun w => by rw [h0, zero_mul])
  refine hasDegreeLE_congr key (fun w => ?_)
  show f w * g w = ∑ S, ∑ T, c S * c' T * chi (symmDiff S T) w
  rw [hf w, hg w, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun S _ => Finset.sum_congr rfl (fun T _ => ?_))
  rw [← chi_mul_chi]
  ring
end AaronsonAmbainis.Row
