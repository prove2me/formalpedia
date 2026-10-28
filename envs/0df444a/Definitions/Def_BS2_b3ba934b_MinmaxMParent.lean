-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxMParent
-- name    : BS2_b3ba934b_MinmaxMParent
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:29:51.822831+00:00
-- url     : https://prove2.me/theorems/6b2282fc-7e93-425b-ad59-8d5368b898fb
-- title:
--   Sensitivity separation: MinmaxMParent (complete source module)
-- statement:
--   Complete Lean source module `MinmaxMParent` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxMParent.lean; original SHA-256 2035dc3dd90b0f59c297164f7bd736fcf514ea069066215e9fba8fce821ec330; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The oriented-row estimates applied to actual graded min/max parents. -/
import Definitions.Def_BS2_b3ba934b_MinmaxPairM

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem mm_orientation (F : L → (I → Bool) → Bool) (t u : L)
    (x : ((V × Bool) × I) → Bool) (w : V)
    (h : mm F t u (child x w false) (child x w true)=true) :
    ∃ c : Bool, F t (child x w (!c))=true ∧ F u (child x w c)=true := by
  obtain ⟨hl,hr,hupper⟩ := (mm_true F t u _ _).1 h
  rcases hupper with hh | hh
  · exact ⟨false,hr,hh⟩
  · exact ⟨true,hl,hh⟩

theorem minmax_oriented_B_row (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (w : V) (d : ℕ)
    (hd : (failed S F j x w).card=d) (hdq : d ≤ S.tolerance j)
    (hstrong : mm F (P.strongLower d) (P.strongUpper d) (child x w false) (child x w true)=true)
    (a b0 b1 : ℕ) (ha : ABound F (S.guard j) (S.guard i) a)
    (hb0 : BBound F (P.weakLower d) (P.strongLower d) b0)
    (hb1 : BBound F (P.weakUpper d) (P.strongUpper d) b1) :
    (flipsTo (parent S F i) false x).card ≤ b0+b1+((outgoing S w).card-d)*a := by
  obtain ⟨c,hlo,hhi⟩ := mm_orientation F _ _ x w hstrong
  have hj : orientedRow S F (P.strongLower d) (P.strongUpper d) (S.guard j) d x w c :=
    ⟨hlo,hhi,hd.le⟩
  have hsub := parent_down_subset_oriented S F hF i P.weakLower P.weakUpper P.weakLowerMono P.weakUpperMono
    P.weakLowerUpper P.weakDef x w d c (hdq.trans P.tolerances)
  have hc := oriented_down_cover S F hF _ _ _ _ _ _ (P.lowerOrder d hdq) (P.upperOrder d hdq)
    P.guards d x w c hj
  have hg := ordinaryGuardBits_card_le S F (S.guard i) (S.guard j) x w a ha
  change (ordinaryGuardBits S F (S.guard i) (S.guard j) x w).card ≤
    ((outgoing S w).card-(failed S F j x w).card)*a at hg
  rw [hd] at hg
  exact (Finset.card_le_card (hsub.trans hc)).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add
      (orientedBits_card F _ _ x w c b0 b1 (hb0 _ hlo) (hb1 _ hhi)) hg))

/-- The pairM branch at one actual winning middle row. Its downward set is
that of the actual weak parent, and its false condition is the actual next parent. -/
theorem minmax_pairM_parent_row (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j k : L) (P : PairData S F i j) (Q : PairData S F j k)
    (x : ((V × Bool) × I) → Bool) (w : V) (d degree : ℕ)
    (hd : (failed S F j x w).card=d) (hdj : d ≤ S.tolerance j) (hdk : d ≤ S.tolerance k)
    (hstrong : mm F (P.strongLower d) (P.strongUpper d) (child x w false) (child x w true)=true)
    (hxk : parent S F k x=false) (hdegree : (outgoing S w).card=degree)
    (a m0 m1 b0 b1 p : ℕ) (ha : ABound F (S.guard j) (S.guard i) a)
    (hm0 : MBound F (P.weakLower d) (P.strongLower d) (Q.strongLower d) m0)
    (hm1 : MBound F (P.weakUpper d) (P.strongUpper d) (Q.strongUpper d) m1)
    (hb0 : BBound F (P.weakLower d) (Q.strongLower d) b0)
    (hb1 : BBound F (P.weakUpper d) (Q.strongUpper d) b1)
    (hp : PBound F (S.guard k) (S.guard j) (S.guard i) p) :
    (flipsTo (parent S F i) false x).card ≤ pairMCost degree d
      (P.strongLower d) (P.strongUpper d) (Q.strongLower d) (Q.strongUpper d)
      (S.guard j) (S.guard k) a m0 m1 b0 b1 p := by
  obtain ⟨c,hlo,hhi⟩ := mm_orientation F _ _ x w hstrong
  have hj : orientedRow S F (P.strongLower d) (P.strongUpper d) (S.guard j) d x w c :=
    ⟨hlo,hhi,hd.le⟩
  have hk : ¬orientedRow S F (Q.strongLower d) (Q.strongUpper d) (S.guard k) d x w c := by
    intro hr
    have hon := oriented_implies_parent S F hF k Q.strongLower Q.strongUpper Q.strongLowerMono Q.strongUpperMono
      Q.strongLowerUpper Q.strongDef x w d c hdk hr
    rw [hxk] at hon
    contradiction
  have hbound := oriented_pairM_row S F hF _ _ _ _ _ _ _ _ _ (P.lowerOrder d hdj) (P.upperOrder d hdj)
    P.guards Q.guards d degree x w c hj hd hk hdegree a m0 m1 b0 b1 p ha hm0 hm1 hb0 hb1 hp
  exact (Finset.card_le_card (parent_down_subset_oriented S F hF i P.weakLower P.weakUpper P.weakLowerMono
    P.weakUpperMono P.weakLowerUpper P.weakDef x w d c (hdj.trans P.tolerances))).trans hbound

end
end ThreeBoundMinmaxTransfer

#print axioms ThreeBoundMinmaxTransfer.minmax_oriented_B_row
#print axioms ThreeBoundMinmaxTransfer.minmax_pairM_parent_row


