-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxZeroLocal
-- name    : BS2_b3ba934b_MinmaxZeroLocal
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:33:16.454919+00:00
-- url     : https://prove2.me/theorems/3e83dacb-49d0-4374-a59f-989579a58571
-- title:
--   Sensitivity separation: MinmaxZeroLocal (complete source module)
-- statement:
--   Complete Lean source module `MinmaxZeroLocal` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxZeroLocal.lean; original SHA-256 b29ef3089e5e16facda23ae8965ecd5913a21a907aa9565bf0f3c40711e7c4f5; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The two shared-head costs in the strict zero-tolerance min/max transfer. -/
import Definitions.Def_BS2_b3ba934b_MinmaxHeadLocal

set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxZeroLocal
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxHeads ThreeBoundHeadCharge
open scoped Classical
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

def headParts (F : L → (I → Bool) → Bool) (g t u : L)
    (x : Bool → I → Bool) (hit c : Bool) : Finset I :=
  upPart F t u x c ∪ if c=hit then flipsTo (F g) false (x c) else ∅

theorem headParts_card (F : L → (I → Bool) → Bool) (g t u : L)
    (x : Bool → I → Bool) (hit : Bool) (w : V) :
    (headBits w (headParts F g t u x hit)).card =
      (upPart F t u x hit ∪ flipsTo (F g) false (x hit)).card+
        (upPart F t u x (!hit)).card := by
  cases hit <;> simp [headBits_card,headParts,Nat.add_comm]

theorem head_same_bound (F : L → (I → Bool) → Bool) (g t u : L)
    (x : Bool → I → Bool) (c : Bool) (w : V) (a s d : ℕ)
    (he : upPart F t u x (!c)=∅) (ha : (upPart F t u x c).card≤a)
    (hs : (flipsTo (F g) false (x c)).card≤ s)
    (hd : (upPart F t u x c ∪ flipsTo (F g) false (x c)).card≤d) :
    (headBits w (headParts F g t u x c)).card≤ min (a+s) d := by
  rw [headParts_card,he,Finset.card_empty,Nat.add_zero]
  apply le_min
  · exact (Finset.card_union_le _ _).trans (Nat.add_le_add ha hs)
  · exact hd

theorem head_other_bound (F : L → (I → Bool) → Bool) (g t u : L)
    (x : Bool → I → Bool) (c : Bool) (w : V) (a j : ℕ)
    (he : upPart F t u x (!c)=∅) (ha : (upPart F t u x c).card≤a)
    (hj : (flipsTo (F g) false (x (!c))).card≤j) :
    (headBits w (headParts F g t u x (!c))).card≤a+j := by
  rw [headParts_card,he,Finset.empty_union,Bool.not_not]
  omega

theorem up_down_union_le (F : L → (I → Bool) → Bool) (g j k l : L)
    (x : I → Bool) (s : Finset I) (hsub : s⊆flipsTo (F l) true x)
    (d : ℕ) (hd : DBound F g j k l d) (hj : F j x=true) (hk : F k x=false) :
    (s ∪ flipsTo (F g) false x).card≤d := by
  apply le_trans (Finset.card_le_card ?_) (hd x hj hk)
  intro a ha
  rcases Finset.mem_union.mp ha with ha | ha
  · exact Finset.mem_union.mpr (Or.inr (hsub ha))
  · exact Finset.mem_union.mpr (Or.inl ha)

theorem cross_cost (F : L → (I → Bool) → Bool) (hF : Nested F)
    (g t u : L) (hgt : g≤t) (x : Bool → I → Bool) (c : Bool) (w : V)
    (hg : F g (x c)=false) (ht : F t (x (!c))=true)
    (b bu j ju : ℕ) (hb : ABound F g t b) (hbu : ABound F g u bu)
    (hj : BBound F g t j) (hju : BBound F g u ju) :
    (headBits w (headParts F g t u x (!c))).card≤ max (b+ju) (bu+j) := by
  have htf := false_of_nested F hF g t hgt _ hg
  have he : upPart F t u x (!c)=∅ :=
    upPart_empty_partner F t u x (!c) (by simpa only [Bool.not_not] using htf)
  by_cases hu : F u (x (!c))=true
  · apply le_trans (b := b+ju) _ (le_max_left _ _)
    apply head_other_bound F g t u x c w b ju he
    · exact (Finset.card_le_card (upPart_subset_lower F t u x c)).trans (hb _ hg)
    · exact hju _ hu
  · have huf : F u (x (!c))=false := Bool.eq_false_iff.mpr hu
    apply le_trans (b := bu+j) _ (le_max_right _ _)
    apply head_other_bound F g t u x c w bu j he
    · exact (Finset.card_le_card (upPart_subset_upper F t u x c huf)).trans (hbu _ hg)
    · exact hj _ ht

def highCost (a au a2 s j ju d du d2 : ℕ) : ℕ :=
  max (min (a+s) d) (max (min (au+s) du)
    (max (a+ju) (max (au+j) (d2+a2))))

theorem highCost_bounds (a au a2 s j ju d du d2 : ℕ) :
    min (a+s) d≤highCost a au a2 s j ju d du d2 ∧
    min (au+s) du≤highCost a au a2 s j ju d du d2 ∧
    a+ju≤highCost a au a2 s j ju d du d2 ∧
    au+j≤highCost a au a2 s j ju d du d2 ∧
    d2+a2≤highCost a au a2 s j ju d du d2 := by
  unfold highCost
  omega

theorem positive_high_cost (F : L → (I → Bool) → Bool) (hF : Nested F)
    (g gi ti ui tj uj : L) (ht : ti≤tj) (htu : ti≤ui) (hu : ui≤uj)
    (x : Bool → I → Bool) (hit : Bool) (w : V)
    (hguard : ∀ c, F g (x c)=true) (hselected : F gi (x hit)=true)
    (hweak : mm F ti ui (x false) (x true)=false)
    (hsome : F tj (x false)=true ∨ F tj (x true)=true)
    (a au a2 s j ju d du d2 : ℕ)
    (ha : PBound F g ti tj a) (hau : PBound F g ui uj au)
    (ha2 : PBound F tj ui uj a2) (hs : BBound F g gi s)
    (hj : BBound F g tj j) (hju : BBound F g uj ju)
    (hd : DBound F g gi ti tj d) (hdu : DBound F g gi ui uj du)
    (hd2 : DBound F g tj ui uj d2) :
    (headBits w (headParts F g tj uj x hit)).card≤highCost a au a2 s j ju d du d2 := by
  obtain ⟨hmax0,hmax1,hmax2,hmax3,hmax4⟩ := highCost_bounds a au a2 s j ju d du d2
  have hlow (c : Bool) (hc : F ti (x c)=false) :
      (headBits w (headParts F g tj uj x hit)).card≤highCost a au a2 s j ju d du d2 := by
    have hcj := false_of_nested F hF ti tj ht _ hc
    have hcu := false_of_nested F hF ti ui htu _ hc
    have he : upPart F tj uj x (!c)=∅ :=
      upPart_empty_partner F tj uj x (!c) (by simpa only [Bool.not_not] using hcj)
    have hpart : F tj (x (!c))=true := by cases c <;> simp_all
    have hpa := (Finset.card_le_card (upPart_subset_lower F tj uj x c)).trans (ha _ (hguard c) hc)
    by_cases hhit : hit=c
    · subst hit
      exact (head_same_bound F g tj uj x c w a s d he hpa (hs _ hselected)
        (up_down_union_le F g gi ti tj _ _ (upPart_subset_lower F tj uj x c)
          d hd hselected hc)).trans hmax0
    · have hh : hit=(!c) := by cases hit <;> cases c <;> simp_all
      rw [hh]
      by_cases hpU : F uj (x (!c))=true
      · exact (head_other_bound F g tj uj x c w a ju he hpa (hju _ hpU)).trans hmax2
      · have hpUf := Bool.eq_false_iff.mpr hpU
        have hpau := (Finset.card_le_card (upPart_subset_upper F tj uj x c hpUf)).trans
          (hau _ (hguard c) hcu)
        exact (head_other_bound F g tj uj x c w au j he hpau (hj _ hpart)).trans hmax3
  by_cases h0 : F ti (x false)=false
  · exact hlow false h0
  by_cases h1 : F ti (x true)=false
  · exact hlow true h1
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
      (headBits w (headParts F g tj uj x hit)).card≤highCost a au a2 s j ju d du d2 := by
    have he : upPart F tj uj x (!c)=∅ :=
      upPart_empty_partner F tj uj x (!c) (by simpa only [Bool.not_not] using hc)
    have hpart : F tj (x (!c))=true := by cases c <;> simp_all
    have hsub := upPart_subset_upper F tj uj x c (hfUJ (!c))
    have hpa := (Finset.card_le_card hsub).trans (hau _ (hguard c) (hfU c))
    by_cases hhit : hit=c
    · subst hit
      exact (head_same_bound F g tj uj x c w au s du he hpa (hs _ hselected)
        (up_down_union_le F g gi ui uj _ _ hsub du hdu hselected (hfU c))).trans hmax1
    · have hh : hit=(!c) := by cases hit <;> cases c <;> simp_all
      rw [hh]
      exact (head_other_bound F g tj uj x c w au j he hpa (hj _ hpart)).trans hmax3
  by_cases h0j : F tj (x false)=false
  · exact hupper false h0j
  by_cases h1j : F tj (x true)=false
  · exact hupper true h1j
  have htj : ∀ c, F tj (x c)=true := by
    intro c
    cases c <;> (cases he : F tj (x _) <;> simp_all)
  rw [headParts_card]
  have hselectedUnion := up_down_union_le F g tj ui uj _ _
    (upPart_subset_upper F tj uj x hit (hfUJ (!hit))) d2 hd2 (htj hit) (hfU hit)
  have hother := (Finset.card_le_card
    (upPart_subset_upper F tj uj x (!hit) (by simpa only [Bool.not_not] using hfUJ hit))).trans
      (ha2 _ (htj (!hit)) (hfU (!hit)))
  exact (Nat.add_le_add hselectedUnion hother).trans hmax4

end
end ThreeBoundMinmaxZeroLocal

#print axioms ThreeBoundMinmaxZeroLocal.cross_cost
#print axioms ThreeBoundMinmaxZeroLocal.positive_high_cost


