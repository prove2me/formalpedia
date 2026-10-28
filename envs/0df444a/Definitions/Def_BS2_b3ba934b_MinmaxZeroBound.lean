-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxZeroBound
-- name    : BS2_b3ba934b_MinmaxZeroBound
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:51:20.476223+00:00
-- url     : https://prove2.me/theorems/448d3cb7-8d96-4ac1-b478-6bd17b54fe36
-- title:
--   Sensitivity separation: MinmaxZeroBound (complete source module)
-- statement:
--   Complete Lean source module `MinmaxZeroBound` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxZeroBound.lean; original SHA-256 28272e8a8d5b9197fbc3b9dbcce47db5bb0666e3a95ac8a26bab10e7cba2ba93; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The full eight-branch strict min/max zero-tolerance upward bound. -/
import Definitions.Def_BS2_b3ba934b_MinmaxZeroShared

set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxZeroSets
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxHeads
open ThreeBoundHeadCharge ThreeBoundMinmaxZeroLocal
open TournamentHighRows CandidateCoherence ResidualCaps ThreeBoundZeroGeometry
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

def Costs.total {S : Stage L I V} {F : L → (I → Bool) → Bool} {i j : L}
    {P : PairData S F i j} (C : Costs S F i j P) : ℕ :=
  max C.first (max (17*C.b+C.high) (max (19*C.b+C.s)
    (max (19*C.b+C.cross) (max (17*C.b+C.s+C.jc)
      (max (17*C.b+C.cross+C.jc) (17*C.b+3*C.jc))))))

theorem total_branches {S : Stage L I V} {F : L → (I → Bool) → Bool} {i j : L}
    {P : PairData S F i j} (C : Costs S F i j P) :
    C.first≤C.total ∧ 17*C.b+C.high≤C.total ∧ 19*C.b+C.s≤C.total ∧
    19*C.b+C.cross≤C.total ∧ 17*C.b+C.s+C.jc≤C.total ∧
    17*C.b+C.cross+C.jc≤C.total ∧ 17*C.b+3*C.jc≤C.total := by
  unfold Costs.total
  omega

theorem zero_configurations (p g e : ℕ) (hp : p≤1) (hg : g≤3)
    (he : 2*e+(p+g)*(p+g-1)=2*g) :
    (g=0) ∨ (p=0 ∧ g=1 ∧ e=1) ∨ (p=0 ∧ g=2 ∧ e=1) ∨
      (p=0 ∧ g=3 ∧ e=0) ∨ (p=1 ∧ g=1 ∧ e=0) := by
  interval_cases p <;> interval_cases g <;> norm_num at he ⊢ <;> omega

theorem single_external_sharp (S : Stage L I V) (hR : IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (i j : L) (P : PairData S F i j)
    (hq : S.tolerance j=0) (x : ((V×Bool)×I) → Bool) (hoff : parent S F i x=false)
    (hp : positives S F P.strongLower P.strongUpper j x=∅)
    (he : (externalArcs S F P.strongLower P.strongUpper j x).card=1)
    (m a : ℕ) (hm : m≤(highHeads S F P.strongLower P.strongUpper j x).card)
    (hcap : DominatorCardBound S.Adj S.label m a) (C : Costs S F i j P) :
    (flipsTo (parent S F j) true x).card≤
      max ((a-1)*C.b+C.s+(arcs S.Adj (highHeads S F P.strongLower P.strongUpper j x)).card*C.jc)
        ((a-1)*C.b+C.cross+(arcs S.Adj (highHeads S F P.strongLower P.strongUpper j x)).card*C.jc) := by
  obtain ⟨⟨v,w⟩,hE⟩ := Finset.card_eq_one.mp he
  have hn := negative_cleaned_cap S hR F hF i j P hq x m a hm hcap
  have hδ := deleted_eq_external_heads S F hF i j P hq x
  rw [hE] at hδ
  by_cases hw : w∈negativeTargets S F P.strongLower P.strongUpper j x
  · have hd : (deleted S F P.strongLower P.strongUpper j x).card=1 := by
      rw [hδ]
      have hh : ({(v,w)} : Finset (V×V)).filter (fun e => e.2∈negativeTargets S F P.strongLower P.strongUpper j x) = {(v,w)} := by
        ext e
        simp only [Finset.mem_filter,Finset.mem_singleton]
        constructor
        · exact And.left
        · rintro rfl
          exact ⟨rfl,hw⟩
      rw [hh,Finset.image_singleton]
      exact Finset.card_singleton _
    rw [hd] at hn
    have hn' : (negativeTargets S F P.strongLower P.strongUpper j x).card-1≤a-1 := by omega
    have hmul := Nat.mul_le_mul_right C.b hn'
    have hb := no_positive_cross_bound S F hF i j P hq x hoff hp v w hE hw C
    exact (hb.trans (Nat.add_le_add_right (Nat.add_le_add_right hmul _) _)).trans (le_max_right _ _)
  · have hd : (deleted S F P.strongLower P.strongUpper j x).card=0 := by
      rw [hδ]
      simp [hw]
    rw [hd,Nat.add_zero] at hn
    have hmul := Nat.mul_le_mul_right C.b hn
    have hb := no_positive_external_bound S F hF i j P hq x hoff hp v w hE C
    exact (hb.trans (Nat.add_le_add_right (Nat.add_le_add_right hmul _) _)).trans (le_max_left _ _)

theorem zero_bound (S : Stage L I V) (hR : IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (i j : L) (P : PairData S F i j)
    (hq : S.tolerance j=0) (x : ((V×Bool)×I) → Bool) (hoff : parent S F i x=false)
    (caps : Exclusions S) (C : Costs S F i j P) :
    (flipsTo (parent S F j) true x).card≤C.total := by
  obtain ⟨hfirst,hshared,hsource,hsourceCross,hdouble,hdoubleCross,htriple⟩ := total_branches C
  have hp := positive_card_le_one S hR F P.strongLower P.strongUpper j x
  have hg := guard_card_le_three S hR F hF i j P hq x
  have he := external_budget_twice S hR F hF i j P hq x
  have hmark := high_card S F P.strongLower P.strongUpper j hq x
  have hec := external_budget S F hF i j P hq x
  have hdel := deleted_card_le_external S F hF i j P hq x
  rcases zero_configurations _ _ _ hp hg he with hg0 | ⟨hp0,hg1,he1⟩ | ⟨hp0,hg2,he1⟩ |
    ⟨hp0,hg3,he0⟩ | ⟨hp1,hg1,he0⟩
  · exact (no_guard_bound S hR F hF i j P hq x hoff (Finset.card_eq_zero.mp hg0) caps C).trans hfirst
  · have hm : 1≤(highHeads S F P.strongLower P.strongUpper j x).card := by omega
    have ha : (arcs S.Adj (highHeads S F P.strongLower P.strongUpper j x)).card=0 := by omega
    have hb := single_external_sharp S hR F hF i j P hq x hoff
      (Finset.card_eq_zero.mp hp0) he1 1 20 hm caps.source C
    simp only [ha,Nat.zero_mul,Nat.add_zero] at hb
    exact hb.trans (max_le hsource hsourceCross)
  · have hm : 2≤(highHeads S F P.strongLower P.strongUpper j x).card := by omega
    have ha : (arcs S.Adj (highHeads S F P.strongLower P.strongUpper j x)).card=1 := by omega
    have hb := single_external_sharp S hR F hF i j P hq x hoff
      (Finset.card_eq_zero.mp hp0) he1 2 18 hm caps.double C
    simp only [ha,Nat.one_mul] at hb
    exact hb.trans (max_le hdouble hdoubleCross)
  · have hm : 2≤(highHeads S F P.strongLower P.strongUpper j x).card := by omega
    have hδ : (deleted S F P.strongLower P.strongUpper j x).card=0 := by omega
    have hn := negative_cleaned_cap S hR F hF i j P hq x 2 18 hm caps.double
    rw [hδ,Nat.add_zero] at hn
    have hmul := Nat.mul_le_mul_right C.b hn
    have ha : (arcs S.Adj (highHeads S F P.strongLower P.strongUpper j x)).card=3 := by omega
    have hb := no_positive_empty_external_bound S F hF i j P hq x hoff
      (Finset.card_eq_zero.mp hp0) (Finset.card_eq_zero.mp he0) C
    rw [ha] at hb
    exact (hb.trans (Nat.add_le_add_right hmul _)).trans htriple
  · have hm : 2≤(highHeads S F P.strongLower P.strongUpper j x).card := by omega
    have hδ : (deleted S F P.strongLower P.strongUpper j x).card=0 := by omega
    have hn := negative_cleaned_cap S hR F hF i j P hq x 2 18 hm caps.double
    rw [hδ,Nat.add_zero] at hn
    have hmul := Nat.mul_le_mul_right C.b hn
    obtain ⟨u,hpu⟩ := Finset.card_eq_one.mp hp1
    obtain ⟨v,hgv⟩ := Finset.card_eq_one.mp hg1
    have hb := shared_positive_bound S hR F hF i j P hq x hoff u v hpu hgv C
    exact (hb.trans (Nat.add_le_add_right hmul _)).trans hshared

end
end ThreeBoundMinmaxZeroSets

#print axioms ThreeBoundMinmaxZeroSets.zero_bound


