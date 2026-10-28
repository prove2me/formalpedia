-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxZeroRepairs
-- name    : BS2_b3ba934b_MinmaxZeroRepairs
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:45:52.605293+00:00
-- url     : https://prove2.me/theorems/bf4bb9ec-a1cd-451f-85e2-f2129d2b4edf
-- title:
--   Sensitivity separation: MinmaxZeroRepairs (complete source module)
-- statement:
--   Complete Lean source module `MinmaxZeroRepairs` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxZeroRepairs.lean; original SHA-256 847373db3c66456a3a2a345be00f7b77d6d12bdeb19acc5e844774a9a67e281e; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Exact repair sets and the local charges used at tolerance zero. -/
import Definitions.Def_BS2_b3ba934b_MinmaxZeroArcs
import Definitions.Def_BS2_b3ba934b_MinmaxZeroLocal

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

def upBits (F : L → (I → Bool) → Bool) (t u : L)
    (x : ((V × Bool) × I) → Bool) (w : V) : Finset ((V×Bool)×I) :=
  headBits w (upPart F t u (child x w))

def arcBits (S : Stage L I V) (F : L → (I → Bool) → Bool) (j : L)
    (x : ((V × Bool) × I) → Bool) (e : V×V) : Finset ((V×Bool)×I) :=
  liftBits e.2 (S.label e.1 e.2) (flipsTo (F (S.guard j)) false (child x e.2 (S.label e.1 e.2)))

def targetRepairs (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) : Finset ((V×Bool)×I) :=
  (targets S F t u j x).biUnion (upBits F (t 0) (u 0) x)

def guardRepairs (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) : Finset ((V×Bool)×I) :=
  (guardArcs S F t u j x).biUnion (arcBits S F j x)

theorem zero_repair_cover (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (hq : S.tolerance j=0)
    (x : ((V × Bool) × I) → Bool) (hoff : parent S F j x=false) :
    flipsTo (parent S F j) true x⊆targetRepairs S F P.strongLower P.strongUpper j x ∪
      guardRepairs S F P.strongLower P.strongUpper j x := by
  rintro ⟨⟨w,c⟩,a⟩ ha
  rcases repair_cover S F hF i j P x w c a hoff (Finset.mem_filter.mp ha).2 with
    ⟨b,hcan,hpart⟩ | ⟨v,b,hcan,hR,hl,hguard,hpart⟩
  · have he : b=0 := by have := hcan.1; omega
    subst b
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨w,(mem_targets _ _ _ _ _ _ _).mpr hcan,(mem_headBits _ _ _ _ _).mpr ⟨rfl,hpart⟩⟩)
  · have he : b=0 := by have := hcan.1; omega
    subst b
    have hv : v∈guardSources S F P.strongLower P.strongUpper j x :=
      (guards_iff _ _ _ _ _ hq _ _).mpr hcan
    have hw : w∈failed S F j x v := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hR,by simpa only [hl] using hguard⟩
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨(v,w),(mem_guardArcs _ _ _ _ _ _ _ _).mpr ⟨hv,hw⟩,
      (mem_liftBits _ _ _ _ _ _).mpr ⟨rfl,hl.symm,by simpa only [hl] using hpart⟩⟩

theorem targetRepairs_split (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (hq : S.tolerance j=0) (x : ((V × Bool) × I) → Bool) :
    targetRepairs S F t u j x =
      (negativeTargets S F t u j x).biUnion (upBits F (t 0) (u 0) x) ∪
      (positives S F t u j x).biUnion (upBits F (t 0) (u 0) x) := by
  have he : targets S F t u j x=negativeTargets S F t u j x∪positives S F t u j x := by
    rw [negative_eq S F t u j hq,Finset.sdiff_union_of_subset (positive_subset_target S F t u j x)]
  rw [targetRepairs,he,Finset.union_biUnion]

theorem guardRepairs_split (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (hq : S.tolerance j=0)
    (x : ((V × Bool) × I) → Bool) :
    guardRepairs S F P.strongLower P.strongUpper j x =
      (arcs S.Adj (highHeads S F P.strongLower P.strongUpper j x)).biUnion (arcBits S F j x) ∪
      (externalArcs S F P.strongLower P.strongUpper j x).biUnion (arcBits S F j x) := by
  have he : guardArcs S F P.strongLower P.strongUpper j x =
      arcs S.Adj (highHeads S F P.strongLower P.strongUpper j x) ∪
        externalArcs S F P.strongLower P.strongUpper j x := by
    rw [← internalArcs_eq S F hF i j P hq x]
    exact (Finset.filter_union_filter_not_eq _ _).symm
  rw [guardRepairs,he,Finset.union_biUnion]

theorem biUnion_card_bound {A B : Type} [DecidableEq B]
    (S : Finset A) (f : A → Finset B) (b : ℕ) (hb : ∀ w∈S,(f w).card≤b) :
    (S.biUnion f).card≤S.card*b := by
  calc
    _ ≤ ∑ w∈S,(f w).card := Finset.card_biUnion_le
    _ ≤ ∑ _w∈S,b := Finset.sum_le_sum hb
    _ = _ := by simp

theorem negative_upBits_bound (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (hq : S.tolerance j=0)
    (x : ((V × Bool) × I) → Bool) (w : V)
    (hw : w∈negativeTargets S F P.strongLower P.strongUpper j x)
    (b : ℕ) (hb : ABound F (S.guard j) (P.strongLower 0) b) :
    (upBits F (P.strongLower 0) (P.strongUpper 0) x w).card≤b := by
  let c := missing S F j x w
  have hfalse := negative_guard_false S F hF i j P x w hw
  have hcan := negative_target S F P.strongLower P.strongUpper j hq x w hw
  have htf := false_of_nested F hF _ _ (P.guardTarget 0 hcan.1) _ hfalse
  have he : upPart F (P.strongLower 0) (P.strongUpper 0) (child x w) (!c)=∅ :=
    upPart_empty_partner F _ _ _ (!c) (by simpa only [Bool.not_not] using htf)
  rw [upBits,headBits_card]
  apply upPart_sum_one F _ _ _ c b he
  exact (Finset.card_le_card (upPart_subset_lower F _ _ _ c)).trans (hb _ hfalse)

theorem positive_upBits_bound (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (hoff : parent S F i x=false) (w : V)
    (hw : w∈positives S F P.strongLower P.strongUpper j x)
    (a au a2 : ℕ) (ha : PBound F (S.guard j) (P.weakLower 0) (P.strongLower 0) a)
    (hau : PBound F (S.guard j) (P.weakUpper 0) (P.strongUpper 0) au)
    (ha2 : PBound F (P.strongLower 0) (P.weakUpper 0) (P.strongUpper 0) a2) :
    (upBits F (P.strongLower 0) (P.strongUpper 0) x w).card≤ max a (max au (2*a2)) := by
  have hp := (mem_positives _ _ _ _ _ _ _).mp hw
  rw [upBits,headBits_card]
  exact minmax_positive_cost F hF _ _ _ _ _ (P.lowerOrder 0 hp.1.1) (P.upperOrder 0 hp.1.1)
    (child x w) hp.2 (weak_target_false S F hF i j P x hoff w 0 hp.1.1 hp.1.2.1.le)
    a au a2 ha hau ha2

theorem arcBits_card (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (j : L) (x : ((V × Bool) × I) → Bool) (e : V×V) :
    (arcBits S F j x e).card=(flipsTo (F (S.guard j)) false (child x e.2 (S.label e.1 e.2))).card := by
  exact card_liftBits _ _ _

theorem external_arc_bound (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (hq : S.tolerance j=0)
    (x : ((V × Bool) × I) → Bool) (hoff : parent S F i x=false) (e : V×V)
    (he : e∈guardArcs S F P.strongLower P.strongUpper j x)
    (s : ℕ) (hs : BBound F (S.guard j) (S.guard i) s) : (arcBits S F j x e).card≤ s := by
  obtain ⟨hv,hw⟩ := (mem_guardArcs _ _ _ _ _ _ _ _).mp he
  rw [arcBits_card]
  exact hs _ (guard_hit_eligible S F hF i j P x hoff e.1 0
    ((guards_iff _ _ _ _ _ hq _ _).mp hv) e.2 hw)

theorem internal_arc_bound (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (hq : S.tolerance j=0)
    (x : ((V × Bool) × I) → Bool) (hp : positives S F P.strongLower P.strongUpper j x=∅)
    (e : V×V) (he : e∈arcs S.Adj (highHeads S F P.strongLower P.strongUpper j x))
    (jcost : ℕ) (hj : BBound F (S.guard j) (P.strongLower 0) jcost) :
    (arcBits S F j x e).card≤jcost := by
  have hwH := ((mem_arcs _ _ _ _).mp he).2.1
  rw [high_eq S F P.strongLower P.strongUpper j hq,hp,Finset.empty_union] at hwH
  have ht := (mm_true F _ _ _ _).mp ((guards_iff _ _ _ _ _ hq _ _).mp hwH).2.2
  rw [arcBits_card]
  apply hj
  cases h : S.label e.1 e.2
  · exact ht.1
  · exact ht.2.1

theorem upBits_union_arcBits (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u j : L) (x : ((V × Bool) × I) → Bool) (v w : V) :
    upBits F t u x w∪arcBits S F j x (v,w)=
      headBits w (headParts F (S.guard j) t u (child x w) (S.label v w)) := by
  ext bit
  rcases bit with ⟨⟨z,c⟩,a⟩
  simp only [upBits,arcBits,Finset.mem_union,mem_headBits,mem_liftBits,headParts]
  by_cases hc : c=S.label v w <;> simp only [hc,if_true,if_false,Finset.notMem_empty,or_false] <;> tauto

theorem cross_upBits_arcBits_bound (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (hq : S.tolerance j=0)
    (x : ((V × Bool) × I) → Bool) (v w : V)
    (hw : w∈negativeTargets S F P.strongLower P.strongUpper j x)
    (he : (v,w)∈guardArcs S F P.strongLower P.strongUpper j x)
    (b bu jc ju : ℕ) (hb : ABound F (S.guard j) (P.strongLower 0) b)
    (hbu : ABound F (S.guard j) (P.strongUpper 0) bu)
    (hj : BBound F (S.guard j) (P.strongLower 0) jc)
    (hju : BBound F (S.guard j) (P.strongUpper 0) ju) :
    (upBits F (P.strongLower 0) (P.strongUpper 0) x w∪arcBits S F j x (v,w)).card≤ max (b+ju) (bu+jc) := by
  let c := missing S F j x w
  have hf := negative_guard_false S F hF i j P x w hw
  have hcan := negative_target S F P.strongLower P.strongUpper j hq x w hw
  have hew := ((mem_guardArcs _ _ _ _ _ _ _ _).mp he).2
  have hl : S.label v w≠c := by
    intro hh
    have ht := (Finset.mem_filter.mp hew).2.2
    rw [hh,hf] at ht
    contradiction
  have hlabel : S.label v w=(!c) := by
    cases h : S.label v w <;> cases hc : c <;> simp_all
  have htf := false_of_nested F hF _ _ (P.guardTarget 0 hcan.1) _ hf
  have hpartner : F (P.strongLower 0) (child x w (!c))=true := by
    have hh := hcan.2.2.2
    change F (P.strongLower 0) (child x w c)=false at htf
    cases hc : c <;> simp_all
  rw [upBits_union_arcBits,hlabel]
  exact cross_cost F hF _ _ _ (P.guardTarget 0 hcan.1) (child x w) c w hf hpartner b bu jc ju hb hbu hj hju

end
end ThreeBoundMinmaxZeroSets

#print axioms ThreeBoundMinmaxZeroSets.zero_repair_cover
#print axioms ThreeBoundMinmaxZeroSets.cross_upBits_arcBits_bound


