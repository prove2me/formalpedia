-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxZeroArcs
-- name    : BS2_b3ba934b_MinmaxZeroArcs
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:41:53.793384+00:00
-- url     : https://prove2.me/theorems/d51ec401-9c4f-4a6a-963c-daaa1d5b604b
-- title:
--   Sensitivity separation: MinmaxZeroArcs (complete source module)
-- statement:
--   Complete Lean source module `MinmaxZeroArcs` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxZeroArcs.lean; original SHA-256 f911f2dcee3af0063db2214e78b0dbe3a562313c8be437f32e69ed65a4f8a662; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- All actual zero-tolerance guard arcs and their exact external budget. -/
import Definitions.Def_BS2_b3ba934b_MinmaxZeroSets

set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxZeroSets
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates
open TournamentHighRows CandidateCoherence ResidualCaps ThreeBoundZeroGeometry
open ThreeBoundActualEnumeration (guardFailures_eq)
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

def guardArcs (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) : Finset (V×V) :=
  (guardSources S F t u j x).biUnion fun v => ({v} : Finset V).product (failed S F j x v)

def externalArcs (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) : Finset (V×V) :=
  (guardArcs S F t u j x).filter fun e => e.2∉highHeads S F t u j x

theorem mem_guardArcs (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (v w : V) :
    (v,w)∈guardArcs S F t u j x ↔ v∈guardSources S F t u j x ∧ w∈failed S F j x v := by
  constructor
  · intro he
    obtain ⟨v',hv',he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨he,hw⟩ := Finset.mem_product.mp he
    have he : v=v' := Finset.mem_singleton.mp he
    subst v'
    exact ⟨hv',hw⟩
  · rintro ⟨hv,hw⟩
    exact Finset.mem_biUnion.mpr ⟨v,hv,Finset.mem_product.mpr ⟨Finset.mem_singleton_self _,hw⟩⟩

theorem guardArcs_card (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u : ℕ → L) (j : L) (hq : S.tolerance j=0) (x : ((V × Bool) × I) → Bool) :
    (guardArcs S F t u j x).card=(guardSources S F t u j x).card := by
  have hd : ((guardSources S F t u j x) : Set V).PairwiseDisjoint
      (fun v => ({v} : Finset V).product (failed S F j x v)) := by
    intro v hv w hw hn
    apply Finset.disjoint_left.mpr
    rintro ⟨z,a⟩ hzv hzw
    have hvz : z=v := Finset.mem_singleton.mp (Finset.mem_product.mp hzv).1
    have hwz : z=w := Finset.mem_singleton.mp (Finset.mem_product.mp hzw).1
    exact hn (hvz.symm.trans hwz)
  unfold guardArcs
  rw [Finset.card_biUnion hd]
  calc
    _ = ∑ _v∈guardSources S F t u j x, 1 := by
      apply Finset.sum_congr rfl
      intro v hv
      calc
        _ = ({v} : Finset V).card*(failed S F j x v).card := Finset.card_product _ _
        _ = 1 := by
          rw [Finset.card_singleton,one_mul]
          exact ((guards_iff S F t u j hq x v).mp hv).2.1
    _ = _ := by simp

theorem internalArcs_eq (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (hq : S.tolerance j=0)
    (x : ((V × Bool) × I) → Bool) :
    (guardArcs S F P.strongLower P.strongUpper j x).filter
      (fun e => e.2∈highHeads S F P.strongLower P.strongUpper j x) =
        arcs S.Adj (highHeads S F P.strongLower P.strongUpper j x) := by
  ext e
  rcases e with ⟨v,w⟩
  simp only [Finset.mem_filter,mem_guardArcs,mem_arcs]
  constructor
  · rintro ⟨⟨hv,hw⟩,hwH⟩
    have hvH : v∈highHeads S F P.strongLower P.strongUpper j x := by
      rw [high_eq S F P.strongLower P.strongUpper j hq]
      exact Finset.mem_union_right _ hv
    exact ⟨hvH,hwH,(Finset.mem_filter.mp hw).2.1⟩
  · rintro ⟨hvH,hwH,hR⟩
    have hw : w∈failed S F j x v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hR,
      high_guards_true S F hF i j P x w hwH (S.label v w)⟩
    have hvG : v∈guardSources S F P.strongLower P.strongUpper j x := by
      by_contra hn
      have hz := high_failure_budget S F P.strongLower P.strongUpper j hq x v hvH
      rw [if_neg hn] at hz
      have hp := Finset.card_pos.mpr ⟨w,hw⟩
      omega
    exact ⟨⟨hvG,hw⟩,hwH⟩

theorem external_budget (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (hq : S.tolerance j=0)
    (x : ((V × Bool) × I) → Bool) :
    (externalArcs S F P.strongLower P.strongUpper j x).card+
      (arcs S.Adj (highHeads S F P.strongLower P.strongUpper j x)).card =
        (guardSources S F P.strongLower P.strongUpper j x).card := by
  have hh := Finset.card_filter_add_card_filter_not
    (s := guardArcs S F P.strongLower P.strongUpper j x)
    (fun e : V×V => e.2∈highHeads S F P.strongLower P.strongUpper j x)
  rw [internalArcs_eq S F hF i j P hq x,guardArcs_card S F P.strongLower P.strongUpper j hq x] at hh
  change _+(externalArcs S F P.strongLower P.strongUpper j x).card=_ at hh
  omega

theorem external_budget_twice (S : Stage L I V) (hR : IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (i j : L) (P : PairData S F i j)
    (hq : S.tolerance j=0) (x : ((V × Bool) × I) → Bool) :
    2*(externalArcs S F P.strongLower P.strongUpper j x).card+
      ((positives S F P.strongLower P.strongUpper j x).card+
        (guardSources S F P.strongLower P.strongUpper j x).card)*
      ((positives S F P.strongLower P.strongUpper j x).card+
        (guardSources S F P.strongLower P.strongUpper j x).card-1)=
      2*(guardSources S F P.strongLower P.strongUpper j x).card := by
  have he := external_budget S F hF i j P hq x
  have ha := twice_arcs_card S.Adj hR (highHeads S F P.strongLower P.strongUpper j x)
  rw [high_card S F P.strongLower P.strongUpper j hq x] at ha
  rw [Nat.mul_sub_left_distrib,Nat.mul_one]
  omega

theorem deleted_eq_external_heads (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (hq : S.tolerance j=0)
    (x : ((V × Bool) × I) → Bool) :
    deleted S F P.strongLower P.strongUpper j x =
      ((externalArcs S F P.strongLower P.strongUpper j x).filter fun e =>
        e.2∈negativeTargets S F P.strongLower P.strongUpper j x).image Prod.snd := by
  ext w
  constructor
  · intro hw
    obtain ⟨v,hv,hw⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨hwN,hR,hlabel⟩ := Finset.mem_filter.mp hw
    have hguard := target_partner_guard S F hF i j P x w 0
      (negative_target S F P.strongLower P.strongUpper j hq x w hwN) (S.label v w) hlabel
    have hwf : w∈failed S F j x v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hR,hguard⟩
    have hvG : v∈guardSources S F P.strongLower P.strongUpper j x := by
      by_contra hn
      have hz := high_failure_budget S F P.strongLower P.strongUpper j hq x v hv
      rw [if_neg hn] at hz
      have hp := Finset.card_pos.mpr ⟨w,hwf⟩
      omega
    apply Finset.mem_image.mpr
    refine ⟨(v,w),Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_,?_⟩,hwN⟩,rfl⟩
    · exact (mem_guardArcs _ _ _ _ _ _ _ _).mpr ⟨hvG,hwf⟩
    · exact (Finset.mem_sdiff.mp hwN).2
  · intro hw
    obtain ⟨⟨v,z⟩,he,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨he,hwN⟩ := Finset.mem_filter.mp he
    obtain ⟨he,hwH⟩ := Finset.mem_filter.mp he
    obtain ⟨hvG,hwf⟩ := (mem_guardArcs _ _ _ _ _ _ _ _).mp he
    have hvH : v∈highHeads S F P.strongLower P.strongUpper j x := by
      rw [high_eq S F P.strongLower P.strongUpper j hq]
      exact Finset.mem_union_right _ hvG
    have hmiss := negative_guard_false S F hF i j P x z hwN
    have hlabel : S.label v z≠missing S F j x z := by
      intro hh
      have ht := (Finset.mem_filter.mp hwf).2.2
      rw [hh,hmiss] at ht
      contradiction
    exact Finset.mem_biUnion.mpr ⟨v,hvH,Finset.mem_filter.mpr
      ⟨hwN,(Finset.mem_filter.mp hwf).2.1,hlabel⟩⟩

theorem deleted_card_le_external (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (hq : S.tolerance j=0)
    (x : ((V × Bool) × I) → Bool) :
    (deleted S F P.strongLower P.strongUpper j x).card≤
      (externalArcs S F P.strongLower P.strongUpper j x).card := by
  rw [deleted_eq_external_heads S F hF i j P hq x]
  exact (Finset.card_image_le).trans (Finset.card_filter_le _ _)

end
end ThreeBoundMinmaxZeroSets

#print axioms ThreeBoundMinmaxZeroSets.external_budget_twice
#print axioms ThreeBoundMinmaxZeroSets.deleted_eq_external_heads


