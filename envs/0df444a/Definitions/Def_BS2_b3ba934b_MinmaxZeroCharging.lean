-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxZeroCharging
-- name    : BS2_b3ba934b_MinmaxZeroCharging
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:47:49.513984+00:00
-- url     : https://prove2.me/theorems/7ae9467c-98ec-4119-b567-4d9b99fb1bb1
-- title:
--   Sensitivity separation: MinmaxZeroCharging (complete source module)
-- statement:
--   Complete Lean source module `MinmaxZeroCharging` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxZeroCharging.lean; original SHA-256 26240c43cfe127a13d71909ee44f26442572134e381c4cbb0fc13b099367306f; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Sharp zero-tolerance repair charging, including the unique external arc. -/
import Definitions.Def_BS2_b3ba934b_MinmaxZeroRepairs

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

structure Costs (S : Stage L I V) (F : L → (I → Bool) → Bool) (i j : L) (P : PairData S F i j) where
  a : ℕ
  au : ℕ
  a2 : ℕ
  b : ℕ
  bu : ℕ
  s : ℕ
  jc : ℕ
  ju : ℕ
  d : ℕ
  du : ℕ
  d2 : ℕ
  ha : PBound F (S.guard j) (P.weakLower 0) (P.strongLower 0) a
  hau : PBound F (S.guard j) (P.weakUpper 0) (P.strongUpper 0) au
  ha2 : PBound F (P.strongLower 0) (P.weakUpper 0) (P.strongUpper 0) a2
  hb : ABound F (S.guard j) (P.strongLower 0) b
  hbu : ABound F (S.guard j) (P.strongUpper 0) bu
  hs : BBound F (S.guard j) (S.guard i) s
  hj : BBound F (S.guard j) (P.strongLower 0) jc
  hju : BBound F (S.guard j) (P.strongUpper 0) ju
  hd : DBound F (S.guard j) (S.guard i) (P.weakLower 0) (P.strongLower 0) d
  hdu : DBound F (S.guard j) (S.guard i) (P.weakUpper 0) (P.strongUpper 0) du
  hd2 : DBound F (S.guard j) (P.strongLower 0) (P.weakUpper 0) (P.strongUpper 0) d2

def Costs.positive {S : Stage L I V} {F : L → (I → Bool) → Bool} {i j : L}
    {P : PairData S F i j} (C : Costs S F i j P) : ℕ := max C.a (max C.au (2*C.a2))
def Costs.cross {S : Stage L I V} {F : L → (I → Bool) → Bool} {i j : L}
    {P : PairData S F i j} (C : Costs S F i j P) : ℕ := max (C.b+C.ju) (C.bu+C.jc)
def Costs.high {S : Stage L I V} {F : L → (I → Bool) → Bool} {i j : L}
    {P : PairData S F i j} (C : Costs S F i j P) : ℕ :=
  highCost C.a C.au C.a2 C.s C.jc C.ju C.d C.du C.d2

theorem repairs_bound (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (hq : S.tolerance j=0)
    (x : ((V × Bool) × I) → Bool) (hoff : parent S F i x=false)
    (C : Costs S F i j P) :
    (targetRepairs S F P.strongLower P.strongUpper j x).card≤
      (negativeTargets S F P.strongLower P.strongUpper j x).card*C.b+
        (positives S F P.strongLower P.strongUpper j x).card*C.positive := by
  rw [targetRepairs_split S F P.strongLower P.strongUpper j hq x]
  apply (Finset.card_union_le _ _).trans
  exact Nat.add_le_add
    (biUnion_card_bound _ _ C.b (fun w hw => negative_upBits_bound S F hF i j P hq x w hw C.b C.hb))
    (biUnion_card_bound _ _ C.positive (fun w hw => positive_upBits_bound S F hF i j P x hoff w hw
      C.a C.au C.a2 C.ha C.hau C.ha2))

theorem no_positive_cover (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (hq : S.tolerance j=0)
    (x : ((V × Bool) × I) → Bool) (hoff : parent S F i x=false)
    (hp : positives S F P.strongLower P.strongUpper j x=∅) :
    flipsTo (parent S F j) true x⊆
      (negativeTargets S F P.strongLower P.strongUpper j x).biUnion
          (upBits F (P.strongLower 0) (P.strongUpper 0) x) ∪
      (arcs S.Adj (highHeads S F P.strongLower P.strongUpper j x)).biUnion (arcBits S F j x) ∪
      (externalArcs S F P.strongLower P.strongUpper j x).biUnion (arcBits S F j x) := by
  have hh := zero_repair_cover S F hF i j P hq x (strong_false_of_weak_false S F hF i j P x hoff)
  rw [targetRepairs_split S F P.strongLower P.strongUpper j hq x,hp,Finset.biUnion_empty,
    Finset.union_empty,guardRepairs_split S F hF i j P hq x,←Finset.union_assoc] at hh
  exact hh

theorem no_positive_empty_external_bound (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (hq : S.tolerance j=0)
    (x : ((V ×Bool)×I) → Bool) (hoff : parent S F i x=false)
    (hp : positives S F P.strongLower P.strongUpper j x=∅)
    (he : externalArcs S F P.strongLower P.strongUpper j x=∅) (C : Costs S F i j P) :
    (flipsTo (parent S F j) true x).card≤
      (negativeTargets S F P.strongLower P.strongUpper j x).card*C.b+
      (arcs S.Adj (highHeads S F P.strongLower P.strongUpper j x)).card*C.jc := by
  have hh := no_positive_cover S F hF i j P hq x hoff hp
  rw [he,Finset.biUnion_empty,Finset.union_empty] at hh
  apply (Finset.card_le_card hh).trans
  apply (Finset.card_union_le _ _).trans
  exact Nat.add_le_add
    (biUnion_card_bound _ _ C.b (fun w hw => negative_upBits_bound S F hF i j P hq x w hw C.b C.hb))
    (biUnion_card_bound _ _ C.jc (fun e he => internal_arc_bound S F hF i j P hq x hp e he C.jc C.hj))

theorem no_positive_external_bound (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (hq : S.tolerance j=0)
    (x : ((V ×Bool)×I) → Bool) (hoff : parent S F i x=false)
    (hp : positives S F P.strongLower P.strongUpper j x=∅)
    (v w : V) (he : externalArcs S F P.strongLower P.strongUpper j x={(v,w)})
    (C : Costs S F i j P) :
    (flipsTo (parent S F j) true x).card≤
      (negativeTargets S F P.strongLower P.strongUpper j x).card*C.b+C.s+
      (arcs S.Adj (highHeads S F P.strongLower P.strongUpper j x)).card*C.jc := by
  have hh := no_positive_cover S F hF i j P hq x hoff hp
  rw [he,Finset.singleton_biUnion] at hh
  have hn := biUnion_card_bound _ _ C.b
    (fun w hw => negative_upBits_bound S F hF i j P hq x w hw C.b C.hb)
  have hi := biUnion_card_bound _ _ C.jc
    (fun e he => internal_arc_bound S F hF i j P hq x hp e he C.jc C.hj)
  have hmem : (v,w)∈guardArcs S F P.strongLower P.strongUpper j x := by
    have hm : (v,w)∈externalArcs S F P.strongLower P.strongUpper j x := by rw [he]; simp
    exact (Finset.mem_filter.mp hm).1
  have hs := external_arc_bound S F hF i j P hq x hoff (v,w) hmem C.s C.hs
  have hle := (Finset.card_le_card hh).trans (Finset.card_union_le _ _)
  have hle2 := Finset.card_union_le
    ((negativeTargets S F P.strongLower P.strongUpper j x).biUnion
      (upBits F (P.strongLower 0) (P.strongUpper 0) x))
    ((arcs S.Adj (highHeads S F P.strongLower P.strongUpper j x)).biUnion (arcBits S F j x))
  omega

theorem no_positive_cross_bound (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (hq : S.tolerance j=0)
    (x : ((V ×Bool)×I) → Bool) (hoff : parent S F i x=false)
    (hp : positives S F P.strongLower P.strongUpper j x=∅)
    (v w : V) (he : externalArcs S F P.strongLower P.strongUpper j x={(v,w)})
    (hw : w∈negativeTargets S F P.strongLower P.strongUpper j x) (C : Costs S F i j P) :
    (flipsTo (parent S F j) true x).card≤
      ((negativeTargets S F P.strongLower P.strongUpper j x).card-1)*C.b+C.cross+
      (arcs S.Adj (highHeads S F P.strongLower P.strongUpper j x)).card*C.jc := by
  let N := negativeTargets S F P.strongLower P.strongUpper j x
  let U := upBits F (P.strongLower 0) (P.strongUpper 0) x
  let A := (arcs S.Adj (highHeads S F P.strongLower P.strongUpper j x)).biUnion (arcBits S F j x)
  have hwN : w∈N := hw
  have hcover := no_positive_cover S F hF i j P hq x hoff hp
  rw [he,Finset.singleton_biUnion] at hcover
  have hsplit : N.biUnion U=(N.erase w).biUnion U∪U w := by
    calc
      N.biUnion U = (insert w (N.erase w)).biUnion U := congrArg (fun B => B.biUnion U) (Finset.insert_erase hwN).symm
      _ = U w∪(N.erase w).biUnion U := Finset.biUnion_insert
      _ = _ := Finset.union_comm _ _
  have hfinal : flipsTo (parent S F j) true x⊆
      (N.erase w).biUnion U∪(U w∪arcBits S F j x (v,w))∪A := by
    intro bit hb
    have hh := hcover hb
    change bit∈N.biUnion U∪A∪arcBits S F j x (v,w) at hh
    rw [hsplit] at hh
    simp only [Finset.mem_union] at hh ⊢
    tauto
  have hn : ((N.erase w).biUnion U).card≤(N.card-1)*C.b := by
    have hh := biUnion_card_bound (N.erase w) U C.b (fun z hz =>
      negative_upBits_bound S F hF i j P hq x z (Finset.mem_of_mem_erase hz) C.b C.hb)
    simpa only [Finset.card_erase_of_mem hwN] using hh
  have hi : A.card≤(arcs S.Adj (highHeads S F P.strongLower P.strongUpper j x)).card*C.jc :=
    biUnion_card_bound _ _ C.jc
      (fun e he => internal_arc_bound S F hF i j P hq x hp e he C.jc C.hj)
  have hmem : (v,w)∈guardArcs S F P.strongLower P.strongUpper j x := by
    have hm : (v,w)∈externalArcs S F P.strongLower P.strongUpper j x := by rw [he]; simp
    exact (Finset.mem_filter.mp hm).1
  have hc := cross_upBits_arcBits_bound S F hF i j P hq x v w hw hmem
    C.b C.bu C.jc C.ju C.hb C.hbu C.hj C.hju
  change (U w∪arcBits S F j x (v,w)).card≤C.cross at hc
  have hh := (Finset.card_le_card hfinal).trans (Finset.card_union_le _ _)
  have hh2 := Finset.card_union_le ((N.erase w).biUnion U) (U w∪arcBits S F j x (v,w))
  change _≤(N.card-1)*C.b+C.cross+_ 
  omega

end
end ThreeBoundMinmaxZeroSets

#print axioms ThreeBoundMinmaxZeroSets.no_positive_cross_bound


