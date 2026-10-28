-- Prove2me | Definitions.Def_BS2_b3ba934b_SelectedBoolCaps
-- name    : BS2_b3ba934b_SelectedBoolCaps
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:07:29.80122+00:00
-- url     : https://prove2.me/theorems/63410892-07a0-450c-9ad9-0cf0c67d8830
-- title:
--   Sensitivity separation: SelectedBoolCaps (complete source module)
-- statement:
--   Complete Lean source module `SelectedBoolCaps` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/SelectedBoolCaps.lean; original SHA-256 dee6213e2a8dd8450bb4d5016caae5e4336c0de164e67fc9b71a2c9b839dbf5e; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The actual Paley-10007 label satisfies the Bool-valued exclusion interfaces
used by the graded-candidate and residual-cap proofs. -/
import Definitions.Def_BS2_b3ba934b_Endpoint40Recipes
import Definitions.Def_BS2_b3ba934b_ResidualCaps

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

namespace Sensitivity10007BoolCaps
open Sensitivity10007Labeling
open scoped Classical BigOperators
noncomputable section

def bit (c : Fin 2) : Bool := decide (c = 1)

def colorBit (b : Bool) : Fin 2 := if b then 1 else 0

theorem bit_eq_iff (c : Fin 2) (b : Bool) : c = colorBit b ↔ bit c = b := by
  fin_cases c <;> cases b <;> decide

theorem bit_ne_iff (c : Fin 2) (b : Bool) : c ≠ colorBit b ↔ bit c ≠ b :=
  not_congr (bit_eq_iff c b)

def boolLabel {V : Type} (ell : V × V → Fin 2) : V → V → Bool :=
  fun v w => bit (ell (v,w))

variable {V : Type} [Fintype V] [DecidableEq V]

theorem mismatch_eq (R : V → V → Prop) (ell : V × V → Fin 2)
    (A : Finset V) (color : V → Bool) (v : V) :
    ZL.mismatch R ell A (fun w => colorBit (color w)) v =
      CandidateCoherence.mismatch R (boolLabel ell) A color v := by
  ext w
  change (w ∈ A.filter (fun z => R v z ∧ ell (v,z) ≠ colorBit (color z))) ↔
    (w ∈ A.filter (fun z => R v z ∧ bit (ell (v,z)) ≠ color z))
  simp only [Finset.mem_filter, bit_ne_iff]

theorem ordinary_of_exclusion (R : V → V → Prop) (ell : V × V → Fin 2) (q a : ℕ)
    (hex : ∀ J : ZL.OrdinaryIndex V a, ¬ (ZL.ordinaryFamily R q a).bad J ell) :
    CandidateCoherence.NoOrdinary R (boolLabel ell) q a := by
  intro A ha color hg
  let J : ZL.OrdinaryIndex V a :=
    ⟨A,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,ha⟩⟩
  apply hex J
  refine ⟨fun w => colorBit (color w),?_⟩
  intro v hv
  simpa only [mismatch_eq] using hg v hv

theorem coherent_of_zero (R : V → V → Prop) (ell : V × V → Fin 2)
    (A M : Finset V) (color : V → Bool)
    (hz : ∀ v ∈ A ∪ M,
      (CandidateCoherence.mismatch R (boolLabel ell) A color v).card = 0) :
    ZL.Coherent R ell A M (fun w => colorBit (color w)) := by
  intro e he
  have hh : e.1 ∈ A ∪ M ∧ e.2 ∈ A ∧ R e.1 e.2 := by
    rcases Finset.mem_union.mp he with hi | hc
    · obtain ⟨hp,hr⟩ := Finset.mem_filter.mp hi
      obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
      exact ⟨Finset.mem_union_left _ hx,hy,hr⟩
    · obtain ⟨hp,hr⟩ := Finset.mem_filter.mp hc
      obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
      exact ⟨Finset.mem_union_right _ hx,hy,hr⟩
  apply (bit_eq_iff _ _).mpr
  by_contra hn
  have hm : e.2 ∈ CandidateCoherence.mismatch R (boolLabel ell) A color e.1 :=
    Finset.mem_filter.mpr ⟨hh.2.1,hh.2.2,hn⟩
  have hp := Finset.card_pos.mpr ⟨e.2,hm⟩
  rw [hz e.1 hh.1] at hp
  omega

theorem coherent_restrict (R : V → V → Prop) (ell : V × V → Fin 2)
    (A A' M : Finset V) (hA : A' ⊆ A) (color : V → Fin 2)
    (hg : ZL.Coherent R ell A M color) : ZL.Coherent R ell A' M color := by
  intro e he
  apply hg e
  rcases Finset.mem_union.mp he with hi | hc
  · obtain ⟨hp,hr⟩ := Finset.mem_filter.mp hi
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hA hx,hA hy⟩,hr⟩)
  · obtain ⟨hp,hr⟩ := Finset.mem_filter.mp hc
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hx,hA hy⟩,hr⟩)

theorem source_of_exclusion (R : V → V → Prop) (ell : V × V → Fin 2) (a : ℕ)
    (hex : ∀ J : ZL.SourceIndex R a, ¬ (ZL.sourceFamily R a).bad J ell) :
    ResidualCaps.DominatorCardBound R (boolLabel ell) 1 a := by
  intro A M color _ hM hdom hz
  obtain ⟨s,rfl⟩ := Finset.card_eq_one.mp hM
  by_contra hn
  obtain ⟨A',hA',hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hn)
  have hsub : A' ⊆ ZL.outOn R Finset.univ s := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hdom s (Finset.mem_singleton_self _) w (hA' hw)⟩
  let J : ZL.SourceIndex R a := ⟨s,⟨A',Finset.mem_powersetCard.mpr ⟨hsub,hcard⟩⟩⟩
  apply hex J
  exact ⟨fun w => colorBit (color w),
    coherent_restrict R ell A A' {s} hA' _ (coherent_of_zero R ell A {s} color hz)⟩

theorem double_of_exclusion (R : V → V → Prop) (ell : V × V → Fin 2) (a : ℕ)
    (hex : ∀ J : ZL.DominatorIndex R a, ¬ (ZL.dominatorFamily R a).bad J ell) :
    ResidualCaps.DominatorCardBound R (boolLabel ell) 2 a := by
  intro A M color _ hM hdom hz
  by_contra hn
  obtain ⟨A',hA',hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hn)
  have hsub : A' ⊆ ZL.dominatedBy R M := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun v hv => hdom v hv w (hA' hw)⟩
  let MI : (Finset.univ : Finset V).powersetCard 2 :=
    ⟨M,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hM⟩⟩
  let J : ZL.DominatorIndex R a := ⟨MI,⟨A',Finset.mem_powersetCard.mpr ⟨hsub,hcard⟩⟩⟩
  apply hex J
  exact ⟨fun w => colorBit (color w),
    coherent_restrict R ell A A' M hA' _ (coherent_of_zero R ell A M color hz)⟩

theorem marked_restrict (R : V → V → Prop) (ell : V → V → Bool)
    (A A' M : Finset V) (hA : A' ⊆ A) (q B : ℕ) (color : V → Bool)
    (hg : ResidualCaps.MarkedGood R ell A M q B color) :
    ResidualCaps.MarkedGood R ell A' M q B color := by
  refine ⟨?_,?_,?_⟩
  · intro v hv
    exact (Nat.add_le_add_right (Finset.card_le_card
      (CandidateCoherence.mismatch_mono R ell A' A hA color v)) _).trans (hg.1 v (hA hv))
  · intro v hv
    exact (Nat.add_le_add_left (Finset.card_le_card
      (CandidateCoherence.mismatch_mono R ell A' A hA color v)) _).trans (hg.2.1 v hv)
  · exact (Finset.sum_le_sum fun v _ => Finset.card_le_card
      (CandidateCoherence.mismatch_mono R ell A' A hA color v)).trans hg.2.2

theorem marked_to_fin (R : V → V → Prop) (ell : V × V → Fin 2)
    (A M : Finset V) (q B : ℕ) (color : V → Bool)
    (hg : ResidualCaps.MarkedGood R (boolLabel ell) A M q B color) :
    ZL.MarkedGood R ell A M ∅ q B (fun w => colorBit (color w)) := by
  have ho (v : V) : ZL.outOn R M v = TournamentHighRows.outNeighbors R M v := rfl
  simpa [ZL.MarkedGood, ResidualCaps.MarkedGood, mismatch_eq, ho]
    using hg

theorem marked_of_exclusion (R : V → V → Prop) (ell : V × V → Fin 2) (q a m B : ℕ)
    (hex : ∀ J : ZL.MarkedIndex V a m, ¬ (ZL.markedFamily R q a m B).bad J ell) :
    ResidualCaps.MarkedCardBound R (boolLabel ell) q m B a := by
  intro A M color hdis hM hg
  by_contra hn
  obtain ⟨A',hA',hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hn)
  have hcompl : A' ⊆ Mᶜ := by
    intro v hv
    exact Finset.mem_compl.mpr (fun hm => Finset.disjoint_left.mp hdis (hA' hv) hm)
  let MI : (Finset.univ : Finset V).powersetCard m :=
    ⟨M,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hM⟩⟩
  let J : ZL.MarkedIndex V a m := ⟨MI,⟨A',Finset.mem_powersetCard.mpr ⟨hcompl,hcard⟩⟩⟩
  apply hex J
  exact ⟨fun w => colorBit (color w),marked_to_fin R ell A' M q B color
    (marked_restrict R (boolLabel ell) A A' M hA' q B color hg)⟩

def label : Fin 10007 → Fin 10007 → Bool := boolLabel Labeling10007.selectedLabel

theorem selected_ordinary (q : Fin 9) :
    CandidateCoherence.NoOrdinary Labeling10007.Adj label q.val
      (CompactLabeling10007.ordinaryA q) :=
  ordinary_of_exclusion _ _ _ _ (Labeling10007.selectedLabel_spec.ordinary q)

theorem selected_source : ResidualCaps.DominatorCardBound Labeling10007.Adj label 1 20 :=
  source_of_exclusion _ _ _ Labeling10007.selectedLabel_spec.source

theorem selected_double : ResidualCaps.DominatorCardBound Labeling10007.Adj label 2 18 :=
  double_of_exclusion _ _ _ Labeling10007.selectedLabel_spec.dominator

theorem selected_marked (i : Fin 12) :
    ResidualCaps.MarkedCardBound Labeling10007.Adj label
      (CompactLabeling10007.marked i).q (CompactLabeling10007.marked i).m
      (CompactLabeling10007.marked i).B (CompactLabeling10007.marked i).a :=
  marked_of_exclusion _ _ _ _ _ _ (Labeling10007.selectedLabel_spec.marked i)

theorem endpoint40_recipe_label (p : Fin 4) :
    (Sensitivity10007Endpoint40.recipe p).label = label := rfl

end
end Sensitivity10007BoolCaps

#print axioms Sensitivity10007BoolCaps.selected_ordinary
#print axioms Sensitivity10007BoolCaps.selected_source
#print axioms Sensitivity10007BoolCaps.selected_double
#print axioms Sensitivity10007BoolCaps.selected_marked


