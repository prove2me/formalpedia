-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxZeroShared
-- name    : BS2_b3ba934b_MinmaxZeroShared
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:49:06.083669+00:00
-- url     : https://prove2.me/theorems/067f17ac-dffa-48ea-b95a-caae23deec82
-- title:
--   Sensitivity separation: MinmaxZeroShared (complete source module)
-- statement:
--   Complete Lean source module `MinmaxZeroShared` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxZeroShared.lean; original SHA-256 f39ab25f49acb17cb1fd7d2b7cd2c4e1c9461434839d5e6508faca96b53996d9; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The two configurations with a positive zero-tolerance target. -/
import Definitions.Def_BS2_b3ba934b_MinmaxZeroCharging

set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxZeroSets
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxHeads
open ThreeBoundHeadCharge ThreeBoundMinmaxZeroLocal
open TournamentHighRows CandidateCoherence ResidualCaps ThreeBoundZeroGeometry
open ThreeBoundActualEnumeration (guardFailures_eq)
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

structure Exclusions (S : Stage L I V) : Prop where
  ordinary : NoOrdinary S.Adj S.label 0 23
  source : DominatorCardBound S.Adj S.label 1 20
  double : DominatorCardBound S.Adj S.label 2 18

def Costs.first {S : Stage L I V} {F : L → (I → Bool) → Bool} {i j : L}
    {P : PairData S F i j} (C : Costs S F i j P) : ℕ := max (22*C.b) (19*C.b+C.positive)

theorem guard_dominates_targets (S : Stage L I V) (hR : IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (i j : L) (P : PairData S F i j)
    (hq : S.tolerance j=0) (x : ((V×Bool)×I) → Bool) :
    ∀ v∈guardSources S F P.strongLower P.strongUpper j x,
      ∀ w∈targets S F P.strongLower P.strongUpper j x, S.Adj v w := by
  apply high_dominates_zero_candidates S.Adj hR S.label (fun z => F (S.guard j) z=true)
    (child x) _ _ (target_guard_disjoint S F P.strongLower P.strongUpper j hq x)
  · intro w hw
    apply high_guards_true S F hF i j P x w
    rw [high_eq S F P.strongLower P.strongUpper j hq]
    exact Finset.mem_union_right _ hw
  · intro w hw
    rw [guardFailures_eq]
    exact ((mem_targets _ _ _ _ _ _ _).mp hw).2.1

theorem shared_guardArcs (S : Stage L I V) (hR : IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (i j : L) (P : PairData S F i j)
    (hq : S.tolerance j=0) (x : ((V×Bool)×I) → Bool) (u v : V)
    (hp : positives S F P.strongLower P.strongUpper j x={u})
    (hg : guardSources S F P.strongLower P.strongUpper j x={v}) :
    guardArcs S F P.strongLower P.strongUpper j x={(v,u)} := by
  have hu : u∈positives S F P.strongLower P.strongUpper j x := by rw [hp]; simp
  have hv : v∈guardSources S F P.strongLower P.strongUpper j x := by rw [hg]; simp
  have hcan := (mem_positives _ _ _ _ _ _ _).mp hu
  have hRvu := guard_dominates_targets S hR F hF i j P hq x v hv u
    (positive_subset_target S F P.strongLower P.strongUpper j x hu)
  have hm : (v,u)∈guardArcs S F P.strongLower P.strongUpper j x :=
    (mem_guardArcs _ _ _ _ _ _ _ _).mpr ⟨hv,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hRvu,hcan.2 (S.label v u)⟩⟩
  have hc : (guardArcs S F P.strongLower P.strongUpper j x).card=1 := by
    rw [guardArcs_card S F P.strongLower P.strongUpper j hq x,hg]
    exact Finset.card_singleton _
  obtain ⟨e,he⟩ := Finset.card_eq_one.mp hc
  have hvu : (v,u)=e := by simpa only [he,Finset.mem_singleton] using hm
  simpa only [←hvu] using he

theorem shared_positive_bound (S : Stage L I V) (hR : IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (i j : L) (P : PairData S F i j)
    (hq : S.tolerance j=0) (x : ((V×Bool)×I) → Bool) (hoff : parent S F i x=false)
    (u v : V) (hp : positives S F P.strongLower P.strongUpper j x={u})
    (hg : guardSources S F P.strongLower P.strongUpper j x={v}) (C : Costs S F i j P) :
    (flipsTo (parent S F j) true x).card≤
      (negativeTargets S F P.strongLower P.strongUpper j x).card*C.b+C.high := by
  have he := shared_guardArcs S hR F hF i j P hq x u v hp hg
  have hh := zero_repair_cover S F hF i j P hq x (strong_false_of_weak_false S F hF i j P x hoff)
  rw [targetRepairs_split S F P.strongLower P.strongUpper j hq x,hp,Finset.singleton_biUnion,
    guardRepairs,he,Finset.singleton_biUnion,Finset.union_assoc] at hh
  have hn := biUnion_card_bound _ _ C.b
    (fun w hw => negative_upBits_bound S F hF i j P hq x w hw C.b C.hb)
  have hu : u∈positives S F P.strongLower P.strongUpper j x := by rw [hp]; simp
  have hv : v∈guardSources S F P.strongLower P.strongUpper j x := by rw [hg]; simp
  have hup := (mem_positives _ _ _ _ _ _ _).mp hu
  have hvg := (guards_iff _ _ _ _ _ hq _ _).mp hv
  have hm : (v,u)∈guardArcs S F P.strongLower P.strongUpper j x := by rw [he]; simp
  have hfail := ((mem_guardArcs _ _ _ _ _ _ _ _).mp hm).2
  have hselected := guard_hit_eligible S F hF i j P x hoff v 0 hvg u hfail
  have hweak := weak_target_false S F hF i j P x hoff u 0 hup.1.1 hup.1.2.1.le
  have hc : (upBits F (P.strongLower 0) (P.strongUpper 0) x u∪arcBits S F j x (v,u)).card≤C.high := by
    rw [upBits_union_arcBits]
    exact positive_high_cost F hF _ _ _ _ _ _ (P.lowerOrder 0 hup.1.1)
      (P.weakLowerUpper 0 (Nat.zero_le _)) (P.upperOrder 0 hup.1.1)
      (child x u) (S.label v u) u hup.2 hselected hweak hup.1.2.2.2
      C.a C.au C.a2 C.s C.jc C.ju C.d C.du C.d2 C.ha C.hau C.ha2 C.hs C.hj C.hju C.hd C.hdu C.hd2
  exact (Finset.card_le_card hh).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add hn hc))

theorem no_guard_bound (S : Stage L I V) (hR : IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (i j : L) (P : PairData S F i j)
    (hq : S.tolerance j=0) (x : ((V×Bool)×I) → Bool) (hoff : parent S F i x=false)
    (hg : guardSources S F P.strongLower P.strongUpper j x=∅)
    (caps : Exclusions S) (C : Costs S F i j P) :
    (flipsTo (parent S F j) true x).card≤C.first := by
  have hga : guardArcs S F P.strongLower P.strongUpper j x=∅ := by
    apply Finset.card_eq_zero.mp
    rw [guardArcs_card S F P.strongLower P.strongUpper j hq x,hg]
    rfl
  have hh := zero_repair_cover S F hF i j P hq x (strong_false_of_weak_false S F hF i j P x hoff)
  rw [guardRepairs,hga,Finset.biUnion_empty,Finset.union_empty] at hh
  have hb := (Finset.card_le_card hh).trans (repairs_bound S F hF i j P hq x hoff C)
  have hp := positive_card_le_one S hR F P.strongLower P.strongUpper j x
  have hδ : (deleted S F P.strongLower P.strongUpper j x).card=0 := by
    have he := external_budget S F hF i j P hq x
    rw [hg,Finset.card_empty] at he
    have hd := deleted_card_le_external S F hF i j P hq x
    omega
  have hmark := high_card S F P.strongLower P.strongUpper j hq x
  rw [hg,Finset.card_empty,Nat.add_zero] at hmark
  by_cases hp0 : (positives S F P.strongLower P.strongUpper j x).card=0
  · have htc := target_cap S F hF i j P x 23 caps.ordinary
    have hpart := target_card S F P.strongLower P.strongUpper j hq x
    have hn : (negativeTargets S F P.strongLower P.strongUpper j x).card≤22 := by omega
    have hm := Nat.mul_le_mul_right C.b hn
    dsimp only [Costs.first]
    have hle : (flipsTo (parent S F j) true x).card≤22*C.b := by
      rw [hp0,Nat.zero_mul,Nat.add_zero] at hb
      exact hb.trans hm
    exact hle.trans (le_max_left _ _)
  · have hm : 1≤(highHeads S F P.strongLower P.strongUpper j x).card := by omega
    have hn := negative_cleaned_cap S hR F hF i j P hq x 1 20 hm caps.source
    rw [hδ] at hn
    have hn19 : (negativeTargets S F P.strongLower P.strongUpper j x).card≤19 := by omega
    have hmul := Nat.mul_le_mul_right C.b hn19
    have hp1 : (positives S F P.strongLower P.strongUpper j x).card=1 := by omega
    rw [hp1,Nat.one_mul] at hb
    exact (hb.trans (Nat.add_le_add_right hmul _)).trans (le_max_right _ _)

theorem guards_empty_of_forbidden (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (hq : S.tolerance j=0)
    (x : ((V×Bool)×I) → Bool) (hoff : parent S F i x=false)
    (hqi : 1≤S.tolerance i) (ht : P.weakLower 1≤P.strongLower 0)
    (hu : P.weakUpper 1≤P.strongUpper 0) : guardSources S F P.strongLower P.strongUpper j x=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  exact guard_forbidden_next S F hF i j P x hoff w 0
    ((guards_iff _ _ _ _ _ hq _ _).mp hw) hqi ht hu

end
end ThreeBoundMinmaxZeroSets

#print axioms ThreeBoundMinmaxZeroSets.shared_positive_bound
#print axioms ThreeBoundMinmaxZeroSets.no_guard_bound


