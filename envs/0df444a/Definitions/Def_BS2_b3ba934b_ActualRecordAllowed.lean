-- Prove2me | Definitions.Def_BS2_b3ba934b_ActualRecordAllowed
-- name    : BS2_b3ba934b_ActualRecordAllowed
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:09:45.971058+00:00
-- url     : https://prove2.me/theorems/079197aa-a897-4f90-8ee6-c00e249fd52d
-- title:
--   Sensitivity separation: ActualRecordAllowed (complete source module)
-- statement:
--   Complete Lean source module `ActualRecordAllowed` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ActualRecordAllowed.lean; original SHA-256 d408a830629b354b8d363d955eb80c684d577e65ca857fd5a57ea69a2a77b324; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Every recipe-dependent filter in the q2 enumeration is satisfied by
the record of an actual input at which the weaker parent is false. -/
import Definitions.Def_BS2_b3ba934b_RecordAllowedAlgorithm
import Definitions.Def_BS2_b3ba934b_ActualCapPrefix
import Definitions.Def_BS2_b3ba934b_ActualKindFilters

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000

namespace ThreeBoundActualRecordAllowed
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundGradedCandidates
open ThreeBoundGradedCover ThreeBoundActualTargets ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundHeadExpressions ThreeBoundAccounting ThreeBoundTypeCounts
open ThreeBoundActualKindFilters ThreeBoundRecordAllowedAlgorithm
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem actual_recordAllowedFor (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry) (matchE : EntryMatch S F i j P a c)
    (input : ((V × Bool) × I) → Bool) (hoff : parent S F i input = false)
    (hQ : S.tolerance j ≤ 2) (tag : V → Fin 8)
    (hk : ∀ w ∈ highHeads S F P.strong j input,
      Q2CandidateTypes.OfKind (fun z => F (S.guard j) z = true)
        (fun k z => F (P.strong k) z = true) (S.tolerance j) (failed S F j input w).card
        (child input w false) (child input w true) (tag w))
    (caps : Caps) (r : Q2Record)
    (hx : ∀ k : Fin 8, r k.val = typeCount (highHeads S F P.strong j input) tag k)
    (hprefix : ∀ k, k ≤ c.tolerance → positivePrefix r k ≤ capPrefix caps r k) :
    recordAllowedFor caps a c r = true := by
  let H := highHeads S F P.strong j input
  have hcQ : c.tolerance ≤ 2 := by rw [← matchE.strongTolerance]; exact hQ
  have hz (kind : Fin 8) (h : ∀ w ∈ H, tag w ≠ kind) : r kind.val = 0 :=
    (hx kind).trans (typeCount_zero_of_forbidden H tag kind h)
  have hguardZero (b : ℕ) (hba : b < a.tolerance)
      (hnext : a.threshold (b+1) ≤ c.threshold b) (kind : Fin 8)
      (hkind : 3 ≤ kind.val) (hlevel : guardLevel kind = b) : r kind.val = 0 := by
    apply hz kind
    intro w hw he
    have hkw := hk w hw
    rw [he] at hkw
    have hg := kind_guard_candidate S F P.strong j input w kind hkw hkind
    rw [hlevel] at hg
    exact actual_guard_filter S F hF i j P a c matchE input hoff w b hg ⟨hba,hnext⟩
  apply recordAllowedFor_of caps a c r
  · apply allowedRecord_of caps c.tolerance r
    · intro hq1
      have hS : S.tolerance j ≤ 1 := by rw [matchE.strongTolerance,hq1]
      have hne (kind : Fin 8) (he : kind.val=2 ∨ kind.val=5 ∨ kind.val=7) : r kind.val=0 := by
        apply hz kind
        intro w hw heq
        have h := actual_kind_tolerance_one S F P.strong j input w (tag w) (hk w hw) hS
        have hv := congrArg Fin.val heq
        rcases he with h2 | h5 | h7 <;> omega
      exact ⟨hne ⟨2,by omega⟩ (Or.inl rfl),
        hne ⟨5,by omega⟩ (Or.inr (Or.inl rfl)),hne ⟨7,by omega⟩ (Or.inr (Or.inr rfl))⟩
    · exact hprefix
  · intro b hb hba hnext
    refine ⟨?_,?_,?_⟩
    · exact hguardZero b hba hnext ⟨3+b,by omega⟩ (by change 3 ≤ 3+b; omega)
        (by simp [guardLevel]; omega)
    · intro hb0
      subst b
      exact hguardZero 0 hba hnext ⟨6,by omega⟩ (by change 3 ≤ 6; decide) (by norm_num [guardLevel])
    · intro hb1
      subst b
      exact hguardZero 1 hba hnext ⟨7,by omega⟩ (by change 3 ≤ 7; decide) (by norm_num [guardLevel])
  · intro b hb hnz
    let kind : Fin 8 := ⟨b,by omega⟩
    have hpos : 0 < typeCount H tag kind := by rw [← hx kind]; exact Nat.pos_of_ne_zero hnz
    obtain ⟨w,hw,he⟩ := nonempty_type_of_count_pos H tag kind hpos
    have hkw := hk w hw
    rw [he] at hkw
    exact actual_positive_filter S F hF i j P a c matchE input hoff w kind hkw (by dsimp [kind]; omega)

end
end ThreeBoundActualRecordAllowed

#print axioms ThreeBoundActualRecordAllowed.actual_recordAllowedFor


