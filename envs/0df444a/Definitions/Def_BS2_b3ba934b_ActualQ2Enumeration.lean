-- Prove2me | Definitions.Def_BS2_b3ba934b_ActualQ2Enumeration
-- name    : BS2_b3ba934b_ActualQ2Enumeration
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:27:30.732824+00:00
-- url     : https://prove2.me/theorems/5379c6b9-b2a2-4eb0-b204-6c59a6a3e954
-- title:
--   Sensitivity separation: ActualQ2Enumeration (complete source module)
-- statement:
--   Complete Lean source module `ActualQ2Enumeration` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ActualQ2Enumeration.lean; original SHA-256 4d53088ce61bfaf7c7afaa0d5b58cdda1e4e981bfa446bc5b0458c6c3ce7297f; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Actual high candidates of the Boolean construction admit one of the
kernel-covered sorted tournament records. -/
import Definitions.Def_BS2_b3ba934b_ActualHeadCosts
import Definitions.Def_BS2_b3ba934b_Q2EnumerationBridge
import Definitions.Def_BS2_b3ba934b_GlobalAccounting

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

namespace ThreeBoundActualEnumeration
open ThreeBoundWitness ThreeBoundProfiles ThreeBoundGradedCandidates ThreeBoundGradedCover
open scoped Classical BigOperators
noncomputable section

theorem card_filter_subtype {V : Type} [Fintype V] (H : Finset V) (p : V → Prop) :
    ((Finset.univ : Finset H).filter fun v => p v.val).card = (H.filter p).card := by
  classical
  apply Finset.card_bij (fun v _ => v.val)
  · intro v hv
    exact Finset.mem_filter.mpr ⟨v.property,(Finset.mem_filter.mp hv).2⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro v hv
    exact ⟨⟨v,(Finset.mem_filter.mp hv).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hv).2⟩,rfl⟩

variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

@[simp] theorem guardFailures_eq (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (j : L) (x : ((V × Bool) × I) → Bool) (v : V) :
    TournamentHighRows.guardFailures S.Adj S.label
      (fun z => F (S.guard j) z = true) (child x) v = failed S F j x v := by
  ext w
  simp [TournamentHighRows.guardFailures,failed]

@[simp] theorem highRows_eq (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (j : L) (t : ℕ → L) (x : ((V × Bool) × I) → Bool) :
    Q2CandidateTypes.highRows S.Adj S.label (fun z => F (S.guard j) z = true)
      (fun b z => F (t b) z = true) (S.tolerance j) (child x) = highHeads S F t j x := by
  ext w
  simp only [Q2CandidateTypes.highRows,highHeads,highAt,Finset.mem_filter,
    Finset.mem_univ,true_and,guardFailures_eq]

theorem actual_high_tags (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (hQ : S.tolerance j ≤ 2) :
    ∃ tag : V → ThreeBoundQ2.Kind,
      (∀ v ∈ highHeads S F P.strong j x,
        Q2CandidateTypes.OfKind (fun z => F (S.guard j) z = true)
          (fun b z => F (P.strong b) z = true) (S.tolerance j)
          (failed S F j x v).card (child x v false) (child x v true) (tag v)) ∧
      (∀ v ∈ highHeads S F P.strong j x,
        (failed S F j x v).card = ThreeBoundQ2.budget (tag v)) ∧
      (∀ v ∈ highHeads S F P.strong j x,
        ((highHeads S F P.strong j x).filter (S.Adj v)).card ≤ ThreeBoundQ2.budget (tag v)) := by
  simpa only [highRows_eq,guardFailures_eq,Q2CandidateTypes.budget_eq_enumerator,
    TournamentHighRows.outNeighbors] using Q2CandidateTypes.actual_high_typed S.Adj S.label
    (fun z => F (S.guard j) z = true) (fun b z => F (P.strong b) z = true)
    (S.tolerance j) hQ (child x)
    (fun b hb z hz => hF _ _ (P.guardTarget b hb) z hz)

theorem actual_record_exists (S : Stage L I V)
    (hR : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (hQ : S.tolerance j ≤ 2)
    (tag : V → ThreeBoundQ2.Kind)
    (hcount : ∀ v ∈ highHeads S F P.strong j x,
      (failed S F j x v).card = ThreeBoundQ2.budget (tag v))
    (hout : ∀ v ∈ highHeads S F P.strong j x,
      ((highHeads S F P.strong j x).filter (S.Adj v)).card ≤ ThreeBoundQ2.budget (tag v)) :
    ∃ (ts : List ThreeBoundQ2.Kind) (ds : List Bool)
      (e : Fin ts.length ≃ highHeads S F P.strong j x),
      ts.Pairwise (· ≤ ·) ∧ (∀ k, ts.get k = tag (e k).val) ∧
      ds = ThreeBoundQ2.orientationBits (fun k l => S.Adj (e k).val (e l).val) ∧
      ThreeBoundQ2.record (ts,ds) ∈ ThreeBoundQ2.records := by
  let H := highHeads S F P.strong j x
  let R : H → H → Prop := fun v w => S.Adj v.val w.val
  have hRH : TournamentHighRows.IsTournament R := by
    constructor
    · exact fun v => hR.loopless v.val
    · intro v w hvw
      exact hR.orient v.val w.val (fun h => hvw (Subtype.ext h))
  have hgt : ∀ b, b ≤ S.tolerance j → ∀ z,
      F (P.strong b) z = true → F (S.guard j) z = true :=
    fun b hb z hz => hF _ _ (P.guardTarget b hb) z hz
  have hcard : H.card ≤ 7 := by
    simpa only [highRows_eq] using Q2CandidateTypes.actual_high_card_le_seven S.Adj hR S.label
      (fun z => F (S.guard j) z = true) (fun b z => F (P.strong b) z = true)
      (S.tolerance j) hQ (child x) hgt
  have hc : ∀ v ∈ Q2CandidateTypes.highRows S.Adj S.label
      (fun z => F (S.guard j) z = true) (fun b z => F (P.strong b) z = true)
      (S.tolerance j) (child x),
      (TournamentHighRows.guardFailures S.Adj S.label
        (fun z => F (S.guard j) z = true) (child x) v).card = Q2CandidateTypes.budget (tag v) := by
    simpa only [highRows_eq,guardFailures_eq,Q2CandidateTypes.budget_eq_enumerator] using hcount
  have hsum : H.card*(H.card-1) ≤ 2*∑ v ∈ H, ThreeBoundQ2.budget (tag v) := by
    simpa only [highRows_eq] using Q2CandidateTypes.actual_high_budget_sum_bound S.Adj hR S.label
      (fun z => F (S.guard j) z = true) (fun b z => F (P.strong b) z = true)
      (S.tolerance j) (child x) hgt tag hc
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
    change ((Finset.univ : Finset H).filter fun v => ThreeBoundQ2.positivePrefix q (tag v.val) = true).card ≤ _
    have he : ((Finset.univ : Finset H).filter fun v =>
        ThreeBoundQ2.positivePrefix q (tag v.val) = true).card =
        (H.filter fun v => ThreeBoundQ2.positivePrefix q (tag v) = true).card := by
      apply Finset.card_bij (fun v _ => v.val)
      · intro v hv
        exact Finset.mem_filter.mpr ⟨v.property,(Finset.mem_filter.mp hv).2⟩
      · intro a _ b _ h
        exact Subtype.ext h
      · intro v hv
        exact ⟨⟨v,(Finset.mem_filter.mp hv).1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hv).2⟩,rfl⟩
    apply he.le.trans
    simpa only [highRows_eq] using Q2CandidateTypes.actual_positive_prefix_card_bound S.Adj hR S.label
      (fun z => F (S.guard j) z = true) (fun b z => F (P.strong b) z = true)
      (S.tolerance j) (child x) hgt tag hc q
  · intro v
    change ((Finset.univ : Finset H).filter fun w => S.Adj v.val w.val).card ≤ _
    rw [card_filter_subtype]
    exact hout v.val v.property

end
end ThreeBoundActualEnumeration

#print axioms ThreeBoundActualEnumeration.actual_high_tags
#print axioms ThreeBoundActualEnumeration.actual_record_exists


