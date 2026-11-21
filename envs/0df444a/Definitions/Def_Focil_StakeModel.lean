-- Prove2me | Definitions.Def_Focil_StakeModel
-- name    : Focil_StakeModel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T23:38:16.023841+00:00
-- url     : https://prove2.me/theorems/fd97da3f-1b10-4647-81ee-c0ec1fa439cc
-- title:
--   Stake Model
-- statement:
--   Definitions and structural lemmas for Stake Model, from Rahul Barman's pinned FOCIL censorship resistance in the nonce model development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/StakeModel.lean

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_Protocol
import Definitions.Def_Focil_ForkChoice
import Definitions.Def_Focil_Safety
set_option autoImplicit false
namespace Focil
theorem filter_count_overlap
    {α : Type} (L : List α) (P Q : α → Bool)
    (h : L.length < (L.filter P).length + (L.filter Q).length) :
    ∃ x, x ∈ L ∧ P x = true ∧ Q x = true := by
  induction L with
  | nil =>
    -- 0 < 0 + 0 is false; the hypothesis is unsatisfiable.
    simp at h
  | cons hd tl ih =>
    -- Decide the head's membership in each filter.
    cases hP : P hd
    · -- P hd = false
      cases hQ : Q hd
      · -- P hd = false, Q hd = false: both filters skip hd.
        rw [List.filter_cons, hP, List.filter_cons, hQ,
            List.length_cons] at h
        simp at h
        obtain ⟨x, hx, hxP, hxQ⟩ := ih (by omega)
        exact ⟨x, List.mem_cons_of_mem _ hx, hxP, hxQ⟩
      · -- P hd = false, Q hd = true: only Q's filter keeps hd.
        rw [List.filter_cons, hP, List.filter_cons, hQ,
            List.length_cons] at h
        simp at h
        obtain ⟨x, hx, hxP, hxQ⟩ := ih (by omega)
        exact ⟨x, List.mem_cons_of_mem _ hx, hxP, hxQ⟩
    · -- P hd = true
      cases hQ : Q hd
      · -- P hd = true, Q hd = false: only P's filter keeps hd.
        rw [List.filter_cons, hP, List.filter_cons, hQ,
            List.length_cons] at h
        simp at h
        obtain ⟨x, hx, hxP, hxQ⟩ := ih (by omega)
        exact ⟨x, List.mem_cons_of_mem _ hx, hxP, hxQ⟩
      · -- P hd = true, Q hd = true: hd itself is the witness.
        exact ⟨hd, List.mem_cons_self, hP, hQ⟩
structure StakeModel where
  /-- Total number of validators. -/
  numValidators : Nat
  /-- Per-validator honesty (Bool for decidability of counts). -/
  honest        : ValidatorIndex → Bool
  /--
    More than two-thirds of validators are honest:
    `3 * |honest| > 2 * numValidators`.
  -/
  honest_majority :
    3 * (((List.range numValidators).filter honest).length) >
      2 * numValidators
structure AttesterRun (s : StakeModel) where
  /-- The fork-choice store at attestation time. -/
  state : FocilState
  /--
    Validity predicate: the formal counterpart of "EVM-valid
    appendability." Bundled here so a concrete instance can
    pin a specific model and the safety chain stays consistent
    end-to-end.
  -/
  canAppend : Transaction → Block → Prop
  /-- The block-fullness model in force. -/
  full  : Block → Prop
  /-- Per-validator/block vote relation (Bool). -/
  voted : ValidatorIndex → Block → Bool
  /--
    Honest-attester compliance: validators flagged honest in
    the underlying `StakeModel` only vote for blocks that are
    FOCIL-compliant against `state` under `canAppend` and
    `full`. This is the only substantive assumption beyond
    honest-supermajority.
  -/
  honest_rule :
    ∀ (v : ValidatorIndex) (b : Block),
      s.honest v = true →
      voted v b = true →
      FocilCompliant canAppend full b state
def AttesterRun.hasQuorum {s : StakeModel} (r : AttesterRun s)
    (b : Block) : Prop :=
  3 * (((List.range s.numValidators).filter
        (fun v => r.voted v b)).length) >
    2 * s.numValidators
def AttesterRun.toForkChoice {s : StakeModel} (r : AttesterRun s) :
    ForkChoice where
  state     := r.state
  canAppend := r.canAppend
  full      := r.full
  IsHonest  := fun v => s.honest v = true
  HasQuorum := fun b => r.hasQuorum b
  Voted     := fun v b => r.voted v b = true
  quorum_has_honest_voter := by
    intro b hQuorum
    have hLen :
        (List.range s.numValidators).length <
        ((List.range s.numValidators).filter s.honest).length +
        ((List.range s.numValidators).filter
          (fun v => r.voted v b)).length := by
      have hH := s.honest_majority
      have hV : 3 * (((List.range s.numValidators).filter
                     (fun v => r.voted v b)).length) >
                2 * s.numValidators := hQuorum
      simp [List.length_range]
      omega
    obtain ⟨v, _hMem, hHonestV, hVotedV⟩ :=
      filter_count_overlap _ _ _ hLen
    exact ⟨v, hHonestV, hVotedV⟩
  honest_attester_compliance := by
    intro b v hHonest hVoted
    exact r.honest_rule v b hHonest hVoted
end Focil


