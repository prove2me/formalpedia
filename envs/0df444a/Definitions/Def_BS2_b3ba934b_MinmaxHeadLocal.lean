-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxHeadLocal
-- name    : BS2_b3ba934b_MinmaxHeadLocal
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:29:59.415989+00:00
-- url     : https://prove2.me/theorems/bd3351a2-30d3-4f2b-a92d-ab0258f5d360
-- title:
--   Sensitivity separation: MinmaxHeadLocal (complete source module)
-- statement:
--   Complete Lean source module `MinmaxHeadLocal` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxHeadLocal.lean; original SHA-256 7b4a4615d6887722b161f9c782f7ffda634731fb755df6d79a5cce601bb7c290; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Actual local upward and two-hit min/max costs. -/
import Definitions.Def_BS2_b3ba934b_MinmaxB
import Definitions.Def_BS2_b3ba934b_HeadCosts

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxHeads
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundHeadCharge
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

def upPart (F : L → (I → Bool) → Bool) (t u : L)
    (x : Bool → I → Bool) (c : Bool) : Finset I :=
  flipsTo (fun z => mm F t u z (x (!c))) true (x c)

theorem upPart_subset_lower (F : L → (I → Bool) → Bool) (t u : L)
    (x : Bool → I → Bool) (c : Bool) : upPart F t u x c ⊆ flipsTo (F t) true (x c) := by
  intro a ha
  have hh := (Finset.mem_filter.mp ha).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,((mm_true F t u _ _).1 hh).1⟩

theorem upPart_subset_upper (F : L → (I → Bool) → Bool) (t u : L)
    (x : Bool → I → Bool) (c : Bool) (ho : F u (x (!c))=false) :
    upPart F t u x c ⊆ flipsTo (F u) true (x c) := by
  intro a ha
  have hh := ((mm_true F t u _ _).1 (Finset.mem_filter.mp ha).2).2.2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  rcases hh with hh | hh
  · exact hh
  · rw [ho] at hh
    contradiction

theorem upPart_empty_partner (F : L → (I → Bool) → Bool) (t u : L)
    (x : Bool → I → Bool) (c : Bool) (ho : F t (x (!c))=false) : upPart F t u x c=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hh := ((mm_true F t u _ _).1 (Finset.mem_filter.mp ha).2).2.1
  rw [ho] at hh
  contradiction

theorem upPart_sum_one (F : L → (I → Bool) → Bool) (t u : L)
    (x : Bool → I → Bool) (c : Bool) (a : ℕ)
    (he : upPart F t u x (!c)=∅) (hb : (upPart F t u x c).card ≤ a) :
    (upPart F t u x false).card+(upPart F t u x true).card ≤ a := by
  cases c <;> simp_all

theorem false_of_nested (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (hij : i ≤ j) (x : I → Bool) (hx : F i x=false) : F j x=false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  have he := hF _ _ hij _ hh
  rw [hx] at he
  contradiction

theorem minmax_positive_cost (F : L → (I → Bool) → Bool) (hF : Nested F)
    (g ti ui tj uj : L) (ht : ti ≤ tj) (hu : ui ≤ uj)
    (x : Bool → I → Bool) (hguard : ∀ c, F g (x c)=true)
    (hweak : mm F ti ui (x false) (x true)=false)
    (a au a2 : ℕ) (ha : PBound F g ti tj a) (hau : PBound F g ui uj au)
    (ha2 : PBound F tj ui uj a2) :
    (upPart F tj uj x false).card+(upPart F tj uj x true).card ≤ max a (max au (2*a2)) := by
  have hlow (c : Bool) (hc : F ti (x c)=false) :
      (upPart F tj uj x false).card+(upPart F tj uj x true).card ≤ a := by
    have hcj := false_of_nested F hF ti tj ht _ hc
    apply upPart_sum_one F tj uj x c a
    · exact upPart_empty_partner F tj uj x (!c) (by simpa only [Bool.not_not] using hcj)
    · exact (Finset.card_le_card (upPart_subset_lower F tj uj x c)).trans (ha _ (hguard c) hc)
  by_cases h0 : F ti (x false)=false
  · exact (hlow false h0).trans (le_max_left _ _)
  by_cases h1 : F ti (x true)=false
  · exact (hlow true h1).trans (le_max_left _ _)
  have hl0 : F ti (x false)=true := by cases he : F ti (x false) <;> simp_all
  have hl1 : F ti (x true)=true := by cases he : F ti (x true) <;> simp_all
  have hfU : ∀ c, F ui (x c)=false := by
    have hh : F ui (x false)=false ∧ F ui (x true)=false := by
      simpa only [mm,hl0,hl1,Bool.and_self,Bool.true_and,Bool.or_eq_false_iff] using hweak
    intro c
    cases c
    · exact hh.1
    · exact hh.2
  have hfUJ (c : Bool) : F uj (x c)=false := false_of_nested F hF ui uj hu _ (hfU c)
  have hupper (c : Bool) (hc : F tj (x c)=false) :
      (upPart F tj uj x false).card+(upPart F tj uj x true).card ≤ au := by
    apply upPart_sum_one F tj uj x c au
    · exact upPart_empty_partner F tj uj x (!c) (by simpa only [Bool.not_not] using hc)
    · exact (Finset.card_le_card (upPart_subset_upper F tj uj x c (hfUJ (!c)))).trans
        (hau _ (hguard c) (hfU c))
  by_cases h0j : F tj (x false)=false
  · exact (hupper false h0j).trans ((le_max_left _ _).trans (le_max_right _ _))
  by_cases h1j : F tj (x true)=false
  · exact (hupper true h1j).trans ((le_max_left _ _).trans (le_max_right _ _))
  have htj : ∀ c, F tj (x c)=true := by
    intro c
    cases c <;> (cases he : F tj (x _) <;> simp_all)
  have hb (c : Bool) : (upPart F tj uj x c).card ≤ a2 :=
    (Finset.card_le_card (upPart_subset_upper F tj uj x c (hfUJ (!c)))).trans
      (ha2 _ (htj c) (hfU c))
  have hh : (upPart F tj uj x false).card+(upPart F tj uj x true).card ≤ 2*a2 := by
    have hh0 := hb false
    have hh1 := hb true
    omega
  exact hh.trans ((le_max_right _ _).trans (le_max_right _ _))

theorem minmax_guard_cost (F : L → (I → Bool) → Bool) (g t u : L)
    (x : Bool → I → Bool) (hit : Finset Bool) (w : V)
    (hmm : mm F t u (x false) (x true)=true)
    (lo hi incoming : ℕ) (hlo : BBound F g t lo) (hhi : BBound F g u hi)
    (hcount : hit.card ≤ incoming) :
    (headBits w (guardParts F g x hit)).card ≤ guardCost lo (lo+hi) incoming := by
  obtain ⟨ht0,ht1,hu⟩ := (mm_true F t u _ _).1 hmm
  have h0 := hlo _ ht0
  have h1 := hlo _ ht1
  have hsum : (flipsTo (F g) false (x false)).card+(flipsTo (F g) false (x true)).card ≤ lo+hi := by
    rcases hu with hu | hu
    · have hh := hhi _ hu
      omega
    · have hh := hhi _ hu
      omega
  apply le_trans (b := guardCost lo (lo+hi) hit.card) _
    (guardCost_mono lo (lo+hi) hit.card incoming (by omega) hcount)
  rw [headBits_card,card_bool_finset]
  by_cases hf : false ∈ hit <;> by_cases ht : true ∈ hit <;>
    simp [guardParts,guardCost,hf,ht] <;> omega

end
end ThreeBoundMinmaxHeads

#print axioms ThreeBoundMinmaxHeads.minmax_positive_cost
#print axioms ThreeBoundMinmaxHeads.minmax_guard_cost


