-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxEnumeration
-- name    : BS2_b3ba934b_MinmaxEnumeration
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:45:21.027804+00:00
-- url     : https://prove2.me/theorems/00ff72b1-6b4a-4746-810c-f03f9808d6b3
-- title:
--   Sensitivity separation: MinmaxEnumeration (complete source module)
-- statement:
--   Complete Lean source module `MinmaxEnumeration` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxEnumeration.lean; original SHA-256 78236771315c364c21bbad73fb0d643b5a7b38998a6835729b542a0105b4736b; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Every actual q2 min/max high-head configuration has a covered record. -/
import Definitions.Def_BS2_b3ba934b_MinmaxQ2Types

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

namespace ThreeBoundMinmaxQ2
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxCaps
open ThreeBoundActualEnumeration (card_filter_subtype guardFailures_eq)
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem actual_record_exists (S : Stage L I V)
    (hR : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (hQ : S.tolerance j ≤ 2)
    (tag : V → ThreeBoundQ2.Kind)
    (hk : ∀ w ∈ highHeads S F P.strongLower P.strongUpper j x,
      ThreeBoundHighTypes.OfKind 2
        (PositiveCandidate S F P.strongLower P.strongUpper j x w)
        (GuardCandidate S F P.strongLower P.strongUpper j x w) (tag w))
    (hout : ∀ v ∈ highHeads S F P.strongLower P.strongUpper j x,
      ((highHeads S F P.strongLower P.strongUpper j x).filter (S.Adj v)).card ≤
        ThreeBoundQ2.budget (tag v)) :
    ∃ (ts : List ThreeBoundQ2.Kind) (ds : List Bool)
      (e : Fin ts.length ≃ highHeads S F P.strongLower P.strongUpper j x),
      ts.Pairwise (· ≤ ·) ∧ (∀ k, ts.get k=tag (e k).val) ∧
      ds=ThreeBoundQ2.orientationBits (fun k l => S.Adj (e k).val (e l).val) ∧
      ThreeBoundQ2.record (ts,ds) ∈ ThreeBoundQ2.records := by
  let H := highHeads S F P.strongLower P.strongUpper j x
  let R : H → H → Prop := fun v w => S.Adj v.val w.val
  have hRH : TournamentHighRows.IsTournament R := by
    constructor
    · exact fun v => hR.loopless v.val
    · intro v w hvw
      exact hR.orient v.val w.val (fun h => hvw (Subtype.ext h))
  have hcard : H.card ≤ 7 := by
    apply TournamentHighRows.card_le_of_outdegree_le S.Adj hR H 3
    intro w hw
    exact (hout w hw).trans (by rw [← budget_eq]; exact ThreeBoundHighTypes.budget_le 2 (tag w))
  have hsum : H.card*(H.card-1) ≤ 2*∑ v ∈ H, ThreeBoundQ2.budget (tag v) :=
    TournamentHighRows.budget_sum_bound S.Adj hR H (fun v => ThreeBoundQ2.budget (tag v)) hout
  apply ThreeBoundQ2.typed_tournament_covered R hRH (fun v => tag v.val)
  · simpa only [Fintype.card_coe] using hcard
  · rw [Fintype.card_coe]
    have hsum' : (∑ v : H, ThreeBoundQ2.budget (tag v.val)) =
        ∑ v ∈ H, ThreeBoundQ2.budget (tag v) := by
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach H (fun v => ThreeBoundQ2.budget (tag v))
    rw [hsum']
    omega
  · intro q _
    change ((Finset.univ : Finset H).filter fun v =>
      ThreeBoundQ2.positivePrefix q (tag v.val)=true).card ≤ _
    have hsub : ((Finset.univ : Finset H).filter fun v =>
        ThreeBoundQ2.positivePrefix q (tag v.val)=true).card =
        (H.filter fun v => ThreeBoundQ2.positivePrefix q (tag v)=true).card := by
      apply Finset.card_bij (fun v _ => v.val)
      · intro v hv
        exact Finset.mem_filter.mpr ⟨v.property,(Finset.mem_filter.mp hv).2⟩
      · intro a _ b _ h
        exact Subtype.ext h
      · intro v hv
        exact ⟨⟨v,(Finset.mem_filter.mp hv).1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hv).2⟩,rfl⟩
    apply hsub.le.trans
    have he := prefix_high_eq S F hF i j P x hQ tag hk q
    change targetPrefix S F P.strongLower P.strongUpper j x q ∩ H = _ at he
    rw [← he]
    apply TournamentHighRows.positive_prefix_card_le S.Adj hR S.label
      (fun z => F (S.guard j) z=true) (child x) _ q
    · intro w hw
      exact high_guards_true S F hF i j P x w (Finset.mem_inter.mp hw).2
    · intro w hw
      exact prefix_guard_budget S F P.strongLower P.strongUpper j x q w (Finset.mem_inter.mp hw).1
  · intro v
    change ((Finset.univ : Finset H).filter fun w => S.Adj v.val w.val).card ≤ _
    rw [card_filter_subtype]
    exact hout v.val v.property

end
end ThreeBoundMinmaxQ2

#print axioms ThreeBoundMinmaxQ2.actual_record_exists


