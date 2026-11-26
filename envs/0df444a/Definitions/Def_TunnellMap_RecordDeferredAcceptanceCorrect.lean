-- Prove2me | Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
-- name    : TunnellMap_RecordDeferredAcceptanceCorrect
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T16:02:23.405656+00:00
-- url     : https://prove2.me/theorems/f64d0c96-e669-4606-96ad-bdceef864148
-- title:
--   Record Deferred Acceptance Correct
-- statement:
--   Definitions and structural lemmas for Record Deferred Acceptance Correct, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordDeferredAcceptanceCorrect.lean

import Definitions.Def_TunnellMap_RecordDeferredAcceptance
import Theorems.Thm_P2M_TunnellMap_GloballyRanked_DAState_nextTarget_getElem__ca19f18bfab1
import Theorems.Thm_TunnellMap_BlockGen_advance_eq_none
import Theorems.Thm_TunnellMap_BlockGen_fullTrace_getElem_key
import Theorems.Thm_TunnellMap_BlockGen_fullTrace_getElem_target
import Theorems.Thm_TunnellMap_BlockGen_orbitTargetLift_injective
import Theorems.Thm_TunnellMap_BlockGen_remainingTrace_initial
import Theorems.Thm_TunnellMap_FreeInvolution_orbit_canonicalRepresentative
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_initial_valid
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_matchingOfTerminal_apply
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_run_queue_nil
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_valid_run
import Theorems.Thm_TunnellMap_GloballyRanked_finalPartner_mem_proposalTargets
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_GloballyRanked_length_preferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
import Theorems.Thm_TunnellMap_OrderedGenerator_mem_orderedIndexList
import Theorems.Thm_TunnellMap_assemble_inl
import Theorems.Thm_TunnellMap_assemble_inr
import Theorems.Thm_TunnellMap_directionKey_negTriple
import Theorems.Thm_TunnellMap_directionKey_primitiveDirection
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_incidentStream_eq_preferenceList
import Theorems.Thm_TunnellMap_keyLeExec_iff
import Theorems.Thm_TunnellMap_keyLtExec_iff
import Theorems.Thm_TunnellMap_minusVector_neg_source
import Theorems.Thm_TunnellMap_minusVector_neg_target
import Theorems.Thm_TunnellMap_plusVector_neg_source
import Theorems.Thm_TunnellMap_plusVector_neg_target
import Theorems.Thm_TunnellMap_polynomialTriple_neg
import Theorems.Thm_TunnellMap_polynomialTriple_triplePolynomial
import Theorems.Thm_TunnellMap_primitiveDirection_idem
import Theorems.Thm_TunnellMap_primitiveDirection_negTriple
import Theorems.Thm_TunnellMap_primitiveDirection_two_vsmul
import Theorems.Thm_TunnellMap_primitivePartTriple_negTriple
import Theorems.Thm_TunnellMap_primitivePartTriple_two_vsmul
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
import Theorems.Thm_TunnellMap_qForm_tau
import Theorems.Thm_TunnellMap_qForm_vsmul
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_source
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_target
import Theorems.Thm_TunnellMap_residualSourceLift_neg
import Theorems.Thm_TunnellMap_residualTargetLift_neg
import Theorems.Thm_TunnellMap_tripleContent_negTriple
import Theorems.Thm_TunnellMap_tripleContent_orientDirection
import Theorems.Thm_TunnellMap_tripleContent_primitiveDirection
import Theorems.Thm_TunnellMap_tripleContent_primitivePartTriple
import Theorems.Thm_TunnellMap_tripleLexLtExec_iff
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_one
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_two
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_zero
import Theorems.Thm_TunnellMap_triplePolynomial_negTriple
import Theorems.Thm_TunnellMap_triplePolynomial_vsmul
attribute [local simp] TunnellMap.BlockGen.remainingTrace_initial
attribute [local simp] TunnellMap.GloballyRanked.DAState.matchingOfTerminal_apply
attribute [local simp] TunnellMap.GloballyRanked.finalPartner_mem_proposalTargets
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.length_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.mem_preferenceList
attribute [local simp] TunnellMap.OrderedGenerator.mem_orderedIndexList
attribute [local simp] TunnellMap.assemble_inl
attribute [local simp] TunnellMap.assemble_inr
attribute [local simp] TunnellMap.directionKey_negTriple
attribute [local simp] TunnellMap.directionKey_primitiveDirection
attribute [local simp] TunnellMap.dot_tau
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.keyLeExec_iff
attribute [local simp] TunnellMap.keyLtExec_iff
attribute [local simp] TunnellMap.minusVector_neg_source
attribute [local simp] TunnellMap.minusVector_neg_target
attribute [local simp] TunnellMap.plusVector_neg_source
attribute [local simp] TunnellMap.plusVector_neg_target
attribute [local simp] TunnellMap.polynomialTriple_neg
attribute [local simp] TunnellMap.polynomialTriple_triplePolynomial
attribute [local simp] TunnellMap.primitiveDirection_idem
attribute [local simp] TunnellMap.primitiveDirection_negTriple
attribute [local simp] TunnellMap.primitiveDirection_two_vsmul
attribute [local simp] TunnellMap.primitivePartTriple_negTriple
attribute [local simp] TunnellMap.primitivePartTriple_two_vsmul
attribute [local simp] TunnellMap.qForm_aLift
attribute [local simp] TunnellMap.qForm_bLift
attribute [local simp] TunnellMap.qForm_tau
attribute [local simp] TunnellMap.qForm_vsmul
attribute [local simp] TunnellMap.representativeEdgeKey_neg_source
attribute [local simp] TunnellMap.representativeEdgeKey_neg_target
attribute [local simp] TunnellMap.residualSourceLift_neg
attribute [local simp] TunnellMap.residualTargetLift_neg
attribute [local simp] TunnellMap.tripleContent_negTriple
attribute [local simp] TunnellMap.tripleContent_orientDirection
attribute [local simp] TunnellMap.tripleContent_primitiveDirection
attribute [local simp] TunnellMap.tripleContent_primitivePartTriple
attribute [local simp] TunnellMap.tripleLexLtExec_iff
attribute [local simp] TunnellMap.triplePolynomial_coeff_one
attribute [local simp] TunnellMap.triplePolynomial_coeff_two
attribute [local simp] TunnellMap.triplePolynomial_coeff_zero
attribute [local simp] TunnellMap.triplePolynomial_negTriple
attribute [local simp] TunnellMap.triplePolynomial_vsmul


set_option autoImplicit true
namespace TunnellMap
namespace GloballyRanked
namespace DAState
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T] (I : GloballyRanked K S T)
omit [LinearOrder K] [Fintype S] [DecidableEq S] [DecidableEq T] in
/-- Two abstract states with the same four data fields are equal. -/
theorem ext' {st₁ st₂ : I.DAState} (hq : st₁.queue = st₂.queue)
    (hc : st₁.cursor = st₂.cursor) (hh : st₁.held = st₂.held)
    (ha : st₁.assigned = st₂.assigned) : st₁ = st₂ := by
  have key : ∀ a b : I.DAState, a.queue = b.queue → a.cursor = b.cursor →
      a.held = b.held → a.assigned = b.assigned → a = b := by
    rintro ⟨q₁, c₁, h₁, a₁, p₁⟩ ⟨q₂, c₂, h₂, a₂, p₂⟩ e₁ e₂ e₃ e₄
    dsimp only at e₁ e₂ e₃ e₄
    subst e₁; subst e₂; subst e₃; subst e₄
    rfl
  exact key _ _ hq hc hh ha
theorem advance_of_held_none (st : I.DAState) (s : S) (rest : List S)
    (h : st.cursor s < Fintype.card T)
    (ht : st.held (st.nextTarget I s h) = none) :
    st.advance I s rest h = st.acceptEmpty I s rest h := by
  simp only [advance]
  split
  · rfl
  · rename_i old hold
    rw [ht] at hold
    exact absurd hold (by simp)
theorem advance_of_replace (st : I.DAState) (s : S) (rest : List S)
    (h : st.cursor s < Fintype.card T) {old : S}
    (ht : st.held (st.nextTarget I s h) = some old)
    (hbetter : I.rank s (st.nextTarget I s h) <
      I.rank old (st.nextTarget I s h)) :
    st.advance I s rest h = st.replaceHeld I s rest h old := by
  simp only [advance]
  split
  · rename_i hold
    rw [ht] at hold
    exact absurd hold (by simp)
  · rename_i old' hold
    rw [ht] at hold
    obtain rfl : old' = old := (Option.some.inj hold).symm
    rw [dif_pos hbetter]
theorem advance_of_reject (st : I.DAState) (s : S) (rest : List S)
    (h : st.cursor s < Fintype.card T) {old : S}
    (ht : st.held (st.nextTarget I s h) = some old)
    (hbetter : ¬ I.rank s (st.nextTarget I s h) <
      I.rank old (st.nextTarget I s h)) :
    st.advance I s rest h = st.rejectProposal I s rest h := by
  simp only [advance]
  split
  · rename_i hold
    rw [ht] at hold
    exact absurd hold (by simp)
  · rename_i old' hold
    rw [ht] at hold
    obtain rfl : old' = old := (Option.some.inj hold).symm
    rw [dif_neg hbetter]
theorem step_of_queue_nil (st : I.DAState) (hq : st.queue = []) :
    st.step I = none := by
  rw [step, hq]
theorem step_of_queue_cons (st : I.DAState) (s : S) (rest : List S)
    (hq : st.queue = s :: rest) (h : st.cursor s < Fintype.card T) :
    st.step I = some (st.advance I s rest h) := by
  rw [step, hq]
  dsimp only
  rw [dif_pos h]
theorem run_of_step_none (st : I.DAState) (h : st.step I = none) :
    st.run I = st := by
  rw [run.eq_1, h]
theorem run_of_step_some (st st' : I.DAState) (h : st.step I = some st') :
    st.run I = st'.run I := by
  rw [run.eq_1, h]
theorem step_eq_none_of_cursor (st : I.DAState) (s : S) (rest : List S)
    (hq : st.queue = s :: rest) (h : ¬ st.cursor s < Fintype.card T) :
    st.step I = none := by
  rw [step, hq]
  dsimp only
  rw [dif_neg h]
@[simp] theorem acceptEmpty_queue (st : I.DAState) (s : S) (rest : List S)
    (h : st.cursor s < Fintype.card T) :
    (st.acceptEmpty I s rest h).queue = rest := rfl
@[simp] theorem acceptEmpty_cursor (st : I.DAState) (s : S) (rest : List S)
    (h : st.cursor s < Fintype.card T) :
    (st.acceptEmpty I s rest h).cursor = st.advancedCursor I s := rfl
@[simp] theorem acceptEmpty_held (st : I.DAState) (s : S) (rest : List S)
    (h : st.cursor s < Fintype.card T) :
    (st.acceptEmpty I s rest h).held =
      Function.update st.held (st.nextTarget I s h) (some s) := rfl
@[simp] theorem acceptEmpty_assigned (st : I.DAState) (s : S) (rest : List S)
    (h : st.cursor s < Fintype.card T) :
    (st.acceptEmpty I s rest h).assigned =
      Function.update st.assigned s (some (st.nextTarget I s h)) := rfl
@[simp] theorem replaceHeld_queue (st : I.DAState) (s : S) (rest : List S)
    (h : st.cursor s < Fintype.card T) (old : S) :
    (st.replaceHeld I s rest h old).queue = rest ++ [old] := rfl
@[simp] theorem replaceHeld_cursor (st : I.DAState) (s : S) (rest : List S)
    (h : st.cursor s < Fintype.card T) (old : S) :
    (st.replaceHeld I s rest h old).cursor = st.advancedCursor I s := rfl
@[simp] theorem replaceHeld_held (st : I.DAState) (s : S) (rest : List S)
    (h : st.cursor s < Fintype.card T) (old : S) :
    (st.replaceHeld I s rest h old).held =
      Function.update st.held (st.nextTarget I s h) (some s) := rfl
@[simp] theorem replaceHeld_assigned (st : I.DAState) (s : S) (rest : List S)
    (h : st.cursor s < Fintype.card T) (old : S) :
    (st.replaceHeld I s rest h old).assigned =
      Function.update (Function.update st.assigned old none) s
        (some (st.nextTarget I s h)) := rfl
@[simp] theorem rejectProposal_queue (st : I.DAState) (s : S) (rest : List S)
    (h : st.cursor s < Fintype.card T) :
    (st.rejectProposal I s rest h).queue = rest ++ [s] := rfl
@[simp] theorem rejectProposal_cursor (st : I.DAState) (s : S) (rest : List S)
    (h : st.cursor s < Fintype.card T) :
    (st.rejectProposal I s rest h).cursor = st.advancedCursor I s := rfl
@[simp] theorem rejectProposal_held (st : I.DAState) (s : S) (rest : List S)
    (h : st.cursor s < Fintype.card T) :
    (st.rejectProposal I s rest h).held = st.held := rfl
@[simp] theorem rejectProposal_assigned (st : I.DAState) (s : S) (rest : List S)
    (h : st.cursor s < Fintype.card T) :
    (st.rejectProposal I s rest h).assigned = st.assigned := rfl
end DAState
end GloballyRanked
namespace RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
open Classical in
/-- The partial inverse of `orbitTargetLift`. -/
noncomputable def orbitOfLift? (hnpos : 0 < n) (v : Triple) :
    Option (aResidualInvolution n hnpos).Orbit :=
  if h : ∃ o, orbitTargetLift hnpos o = v then some h.choose else none
theorem orbitOfLift?_lift (hnpos : 0 < n)
    (o : (aResidualInvolution n hnpos).Orbit) :
    orbitOfLift? hnpos (orbitTargetLift hnpos o) = some o := by
  have hex : ∃ o', orbitTargetLift hnpos o' = orbitTargetLift hnpos o := ⟨o, rfl⟩
  rw [orbitOfLift?, dif_pos hex]
  exact congrArg some (orbitTargetLift_injective hnpos hex.choose_spec)
abbrev orbOf (s : BResidual n) : (bResidualInvolution n).Orbit :=
  (bResidualInvolution n).orbit s
@[simp] theorem orbOf_rep (q : (bResidualInvolution n).Orbit) :
    orbOf (canonicalBResidualRepresentative q) = q :=
  (bResidualInvolution n).orbit_canonicalRepresentative bResidualLexKey
    bResidualLexKey_injective q
theorem rep_orbOf_eq_iff {s : BResidual n}
    (hcanon : canonicalBResidualRepresentative (orbOf s) = s)
    (q : (bResidualInvolution n).Orbit) :
    canonicalBResidualRepresentative q = s ↔ q = orbOf s := by
  constructor
  · intro h; rw [← orbOf_rep q, h]
  · rintro rfl; exact hcanon
variable [Fintype (BOddRep n)] [Fintype (ARep n)]
theorem fullTrace_length_card (hn : Odd n) (hnpos : 0 < n) (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    (fullTrace s F).length =
      Fintype.card (aResidualInvolution n hnpos).Orbit := by
  rw [fullTrace_length_eq hnpos F, incidentStream_eq_preferenceList hn hnpos s F,
    (residualOrbitRanking hnpos).length_preferenceList]
theorem fullTrace_getElem_target_pref (hn : Odd n) (hnpos : 0 < n)
    (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) {k : ℕ}
    (hk : k < (fullTrace s F).length) :
    ((fullTrace s F)[k]'hk).target =
      orbitTargetLift hnpos
        (((residualOrbitRanking hnpos).preferenceList (orbOf s))[k]'(by
          rw [(residualOrbitRanking hnpos).length_preferenceList,
            ← fullTrace_length_card hn hnpos s F]
          exact hk)) := by
  rw [fullTrace_getElem_target hnpos F hk]
  congr 1
  congr 1
  exact incidentStream_eq_preferenceList hn hnpos s F
theorem fullTrace_getElem_key_pref (hn : Odd n) (hnpos : 0 < n)
    (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) {k : ℕ}
    (hk : k < (fullTrace s F).length) :
    ((fullTrace s F)[k]'hk).key =
      (residualOrbitRanking hnpos).rank (orbOf s)
        (((residualOrbitRanking hnpos).preferenceList (orbOf s))[k]'(by
          rw [(residualOrbitRanking hnpos).length_preferenceList,
            ← fullTrace_length_card hn hnpos s F]
          exact hk)) := by
  rw [fullTrace_getElem_key hnpos F hk]
  show orbitEdgeKey hnpos (orbOf s) _ = orbitEdgeKey hnpos (orbOf s) _
  congr 1
  congr 1
  exact incidentStream_eq_preferenceList hn hnpos s F
def cursorOf (frames : FrameFamily n) (E : DARun n) (s : BResidual n) : ℕ :=
  (fullTrace s (frames s)).length -
    (remainingTrace s (frames s) (E.gen s)).length
theorem cursorOf_le_card (hn : Odd n) (hnpos : 0 < n) (frames : FrameFamily n)
    (E : DARun n) (s : BResidual n) :
    cursorOf frames E s ≤ Fintype.card (aResidualInvolution n hnpos).Orbit := by
  rw [cursorOf, ← fullTrace_length_card hn hnpos s (frames s)]
  exact Nat.sub_le _ _
omit [Fintype (BOddRep n)] [Fintype (ARep n)] in
/-- If the generator state is positioned inside the complete trace, one
`advance` step reads exactly the record at the current cursor and moves the
cursor forward by one. -/
theorem step_head_index {frames : FrameFamily n} {E : DARun n}
    {s : BResidual n} {r : IncidentRecord} {g : GenState}
    (hsuf : remainingTrace s (frames s) (E.gen s) <:+ fullTrace s (frames s))
    (hadv : BlockGen.advance s (frames s) (E.gen s) = some (r, g)) :
    ∃ hk : cursorOf frames E s < (fullTrace s (frames s)).length,
      r = (fullTrace s (frames s))[cursorOf frames E s]'hk ∧
        remainingTrace s (frames s) g <:+ fullTrace s (frames s) ∧
        (fullTrace s (frames s)).length -
            (remainingTrace s (frames s) g).length =
          cursorOf frames E s + 1 := by
  set L := (fullTrace s (frames s)).length with hL
  set rem := remainingTrace s (frames s) (E.gen s) with hrem
  have hcons : rem = r :: remainingTrace s (frames s) g := advance_eq_some _ hadv
  have hmle : rem.length ≤ L := hsuf.length_le
  have hdrop : rem = (fullTrace s (frames s)).drop (L - rem.length) :=
    List.suffix_iff_eq_drop.mp hsuf
  have hne : (fullTrace s (frames s)).drop (L - rem.length) ≠ [] := by
    rw [← hdrop, hcons]; simp
  have hk : L - rem.length < L := by
    by_contra hnot
    exact hne (List.drop_eq_nil_iff.mpr (by omega))
  have hcur : cursorOf frames E s = L - rem.length := rfl
  refine ⟨by rw [hcur]; exact hk, ?_, ?_, ?_⟩
  · have hdrop2 := hdrop
    rw [List.drop_eq_getElem_cons hk] at hdrop2
    exact (List.cons.inj (hcons.symm.trans hdrop2)).1
  · have hsuf' : remainingTrace s (frames s) g <:+ rem := by
      rw [hcons]; exact List.suffix_cons _ _
    exact hsuf'.trans hsuf
  · have hlen : rem.length = (remainingTrace s (frames s) g).length + 1 := by
      rw [hcons]; simp
    rw [hcur]; omega
noncomputable def abst (hn : Odd n) (hnpos : 0 < n) (frames : FrameFamily n)
    (E : DARun n) : (residualOrbitRanking hnpos).DAState where
  queue := E.queue.map orbOf
  cursor := fun q => cursorOf frames E (canonicalBResidualRepresentative q)
  held := fun o => (E.held (orbitTargetLift hnpos o)).map fun p => orbOf p.1
  assigned := fun q => (E.assigned (canonicalBResidualRepresentative q)).bind
    fun r => orbitOfLift? hnpos r.target
  cursor_le := fun _ => cursorOf_le_card hn hnpos frames E _
@[simp] theorem abst_queue (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n) (E : DARun n) :
    (abst hn hnpos frames E).queue = E.queue.map orbOf := rfl
@[simp] theorem abst_cursor (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n) (E : DARun n) (q : (bResidualInvolution n).Orbit) :
    (abst hn hnpos frames E).cursor q =
      cursorOf frames E (canonicalBResidualRepresentative q) := rfl
@[simp] theorem abst_held (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n) (E : DARun n)
    (o : (aResidualInvolution n hnpos).Orbit) :
    (abst hn hnpos frames E).held o =
      (E.held (orbitTargetLift hnpos o)).map (fun p => orbOf p.1) := rfl
@[simp] theorem abst_assigned (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n) (E : DARun n) (q : (bResidualInvolution n).Orbit) :
    (abst hn hnpos frames E).assigned q =
      (E.assigned (canonicalBResidualRepresentative q)).bind
        (fun r => orbitOfLift? hnpos r.target) := rfl
structure Sim (hnpos : 0 < n) (frames : FrameFamily n) (E : DARun n) : Prop where
  /-- Every roster entry is the canonical representative of its orbit. -/
  canon : ∀ s ∈ E.sources, canonicalBResidualRepresentative (orbOf s) = s
  /-- The queue only contains roster entries. -/
  queue_sub : ∀ s ∈ E.queue, s ∈ E.sources
  /-- Every generator is positioned inside its complete trace. -/
  suffix : ∀ s : BResidual n,
    remainingTrace s (frames s) (E.gen s) <:+ fullTrace s (frames s)
  /-- Every held record was proposed by a roster entry. -/
  held_src : ∀ v s' r', E.held v = some (s', r') → s' ∈ E.sources
  /-- A held record is stored under its own target. -/
  held_target : ∀ v s' r', E.held v = some (s', r') → r'.target = v
  /-- A held record stores the proposer's rank of the held target. -/
  held_key : ∀ (t : (aResidualInvolution n hnpos).Orbit) s' r',
    E.held (orbitTargetLift hnpos t) = some (s', r') →
      r'.key = (residualOrbitRanking hnpos).rank (orbOf s') t
  /-- Every assigned record points at a lifted residual target orbit. -/
  assigned_lift : ∀ s r, E.assigned s = some r →
    ∃ t : (aResidualInvolution n hnpos).Orbit, r.target = orbitTargetLift hnpos t
omit [Fintype (BOddRep n)] [Fintype (ARep n)] in
theorem rep_eq_iff {s : BResidual n} (hcanon : canonicalBResidualRepresentative (orbOf s) = s)
    (q : (bResidualInvolution n).Orbit) :
    canonicalBResidualRepresentative q = s ↔ q = orbOf s :=
  rep_orbOf_eq_iff hcanon q
theorem abst_cursor_update (hn : Odd n) (hnpos : 0 < n) (frames : FrameFamily n)
    {E E' : DARun n} {s : BResidual n} {g : GenState}
    (hcanon : canonicalBResidualRepresentative (orbOf s) = s)
    (hEg : E'.gen = Function.update E.gen s g)
    (hcurg : (fullTrace s (frames s)).length -
        (remainingTrace s (frames s) g).length = cursorOf frames E s + 1) :
    (abst hn hnpos frames E).advancedCursor (residualOrbitRanking hnpos) (orbOf s)
      = (abst hn hnpos frames E').cursor := by
  funext q
  simp only [DAState.advancedCursor]
  by_cases hq1 : q = orbOf s
  · subst q
    rw [Function.update_self, abst_cursor, abst_cursor, hcanon]
    simp only [cursorOf] at hcurg ⊢
    rw [hEg, Function.update_self]
    exact hcurg.symm
  · have hrep : canonicalBResidualRepresentative q ≠ s := fun hc =>
      hq1 ((rep_eq_iff hcanon q).mp hc)
    rw [Function.update_of_ne hq1, abst_cursor, abst_cursor]
    simp only [cursorOf]
    rw [hEg, Function.update_of_ne hrep]
theorem abst_held_update (hn : Odd n) (hnpos : 0 < n) (frames : FrameFamily n)
    {E E' : DARun n} {s : BResidual n} {r : IncidentRecord}
    {t : (aResidualInvolution n hnpos).Orbit}
    (hrt : r.target = orbitTargetLift hnpos t)
    (hEh : E'.held = Function.update E.held r.target (some (s, r))) :
    Function.update (abst hn hnpos frames E).held t (some (orbOf s))
      = (abst hn hnpos frames E').held := by
  funext o
  by_cases ho : o = t
  · subst o
    rw [Function.update_self, abst_held, hEh, ← hrt, Function.update_self]
    rfl
  · rw [Function.update_of_ne ho, abst_held, abst_held, hEh,
      Function.update_of_ne
        (fun hc => ho (orbitTargetLift_injective hnpos (hc.trans hrt)))]
theorem abst_assigned_update (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n) {E E' : DARun n} {s : BResidual n}
    {r : IncidentRecord} {t : (aResidualInvolution n hnpos).Orbit}
    (hcanon : canonicalBResidualRepresentative (orbOf s) = s)
    (hrt : r.target = orbitTargetLift hnpos t)
    (hEa : E'.assigned = Function.update E.assigned s (some r)) :
    Function.update (abst hn hnpos frames E).assigned (orbOf s) (some t)
      = (abst hn hnpos frames E').assigned := by
  funext q
  by_cases hq1 : q = orbOf s
  · subst q
    rw [Function.update_self, abst_assigned, hcanon, hEa, Function.update_self]
    simp only [Option.bind_some]
    rw [hrt, orbitOfLift?_lift]
  · have hrep : canonicalBResidualRepresentative q ≠ s := fun hc =>
      hq1 ((rep_eq_iff hcanon q).mp hc)
    rw [Function.update_of_ne hq1, abst_assigned, abst_assigned, hEa,
      Function.update_of_ne hrep]
theorem abst_assigned_update_replace (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n) {E E' : DARun n} {s old : BResidual n}
    {r : IncidentRecord} {t : (aResidualInvolution n hnpos).Orbit}
    (hcanon : canonicalBResidualRepresentative (orbOf s) = s)
    (hcanonOld : canonicalBResidualRepresentative (orbOf old) = old)
    (hrt : r.target = orbitTargetLift hnpos t)
    (hEa : E'.assigned =
      Function.update (Function.update E.assigned old none) s (some r)) :
    Function.update
        (Function.update (abst hn hnpos frames E).assigned (orbOf old) none)
        (orbOf s) (some t)
      = (abst hn hnpos frames E').assigned := by
  funext q
  by_cases hq1 : q = orbOf s
  · subst q
    rw [Function.update_self, abst_assigned, hcanon, hEa, Function.update_self]
    simp only [Option.bind_some]
    rw [hrt, orbitOfLift?_lift]
  · have hrep : canonicalBResidualRepresentative q ≠ s := fun hc =>
      hq1 ((rep_eq_iff hcanon q).mp hc)
    rw [Function.update_of_ne hq1]
    by_cases hq2 : q = orbOf old
    · subst q
      have hos : old ≠ s := by rw [← hcanonOld]; exact hrep
      rw [Function.update_self, abst_assigned, hcanonOld, hEa,
        Function.update_of_ne hos, Function.update_self]
      rfl
    · have hrepOld : canonicalBResidualRepresentative q ≠ old := fun hc =>
        hq2 ((rep_eq_iff hcanonOld q).mp hc)
      rw [Function.update_of_ne hq2, abst_assigned, abst_assigned, hEa,
        Function.update_of_ne hrep, Function.update_of_ne hrepOld]
theorem step_none_sim (hn : Odd n) (hnpos : 0 < n) (frames : FrameFamily n)
    {E : DARun n} (hSim : Sim hnpos frames E) (h : step frames E = none) :
    (abst hn hnpos frames E).step (residualOrbitRanking hnpos) = none := by
  by_cases hq0 : E.queue = []
  · exact DAState.step_of_queue_nil _ _ (by rw [abst_queue, hq0, List.map_nil])
  obtain ⟨s, rest, hq⟩ := List.exists_cons_of_ne_nil hq0
  have hsmem : s ∈ E.sources := hSim.queue_sub s (by rw [hq]; simp)
  have hcanon : canonicalBResidualRepresentative (orbOf s) = s := hSim.canon s hsmem
  have hadv : BlockGen.advance s (frames s) (E.gen s) = none := by
    rcases hadvc : BlockGen.advance s (frames s) (E.gen s) with _ | ⟨r, g⟩
    · rfl
    · exfalso
      rcases hheld : E.held r.target with _ | ⟨old, rold⟩
      · rw [step_accept hq hsmem hadvc hheld] at h; exact absurd h (by simp)
      · by_cases hlt : r.key < rold.key
        · rw [step_replace hq hsmem hadvc hheld hlt] at h; exact absurd h (by simp)
        · rw [step_reject hq hsmem hadvc hheld hlt] at h; exact absurd h (by simp)
  have hrem : remainingTrace s (frames s) (E.gen s) = [] := advance_eq_none _ hadv
  refine DAState.step_eq_none_of_cursor _ _ (orbOf s) (rest.map orbOf)
    (by rw [abst_queue, hq, List.map_cons]) ?_
  rw [abst_cursor, hcanon]
  simp only [cursorOf, hrem, List.length_nil, Nat.sub_zero]
  rw [fullTrace_length_card hn hnpos s (frames s)]
  exact lt_irrefl _
theorem step_some_sim (hn : Odd n) (hnpos : 0 < n) (frames : FrameFamily n)
    {E E' : DARun n} (hSim : Sim hnpos frames E) (h : step frames E = some E') :
    Sim hnpos frames E' ∧
      (abst hn hnpos frames E).step (residualOrbitRanking hnpos) =
        some (abst hn hnpos frames E') := by
  by_cases hq0 : E.queue = []
  · rw [step_nil hq0] at h; exact absurd h (by simp)
  obtain ⟨s, rest, hq⟩ := List.exists_cons_of_ne_nil hq0
  have hsmem : s ∈ E.sources := hSim.queue_sub s (by rw [hq]; simp)
  have hcanon : canonicalBResidualRepresentative (orbOf s) = s := hSim.canon s hsmem
  have hqrest : ∀ x ∈ rest, x ∈ E.sources := fun x hx =>
    hSim.queue_sub x (by rw [hq]; exact List.mem_cons_of_mem _ hx)
  rcases hadvc : BlockGen.advance s (frames s) (E.gen s) with _ | ⟨r, g⟩
  · rw [step_exhausted hq hsmem hadvc] at h; exact absurd h (by simp)
  obtain ⟨hk, hrk, hsufg, hcurg⟩ := step_head_index (hSim.suffix s) hadvc
  have hcard : (fullTrace s (frames s)).length =
      Fintype.card (aResidualInvolution n hnpos).Orbit :=
    fullTrace_length_card hn hnpos s (frames s)
  have hklt : cursorOf frames E s <
      Fintype.card (aResidualInvolution n hnpos).Orbit := by rw [← hcard]; exact hk
  have hkpref : cursorOf frames E s <
      ((residualOrbitRanking hnpos).preferenceList (orbOf s)).length := by
    rw [(residualOrbitRanking hnpos).length_preferenceList]; exact hklt
  obtain ⟨t, htdef⟩ : ∃ t, ((residualOrbitRanking hnpos).preferenceList
      (orbOf s))[cursorOf frames E s]'hkpref = t := ⟨_, rfl⟩
  have hcursor_s : (abst hn hnpos frames E).cursor (orbOf s) = cursorOf frames E s := by
    rw [abst_cursor, hcanon]
  have hcurlt : (abst hn hnpos frames E).cursor (orbOf s) <
      Fintype.card (aResidualInvolution n hnpos).Orbit := by
    rw [hcursor_s]; exact hklt
  have hqabs : (abst hn hnpos frames E).queue = orbOf s :: rest.map orbOf := by
    rw [abst_queue, hq, List.map_cons]
  have hnextEq : (abst hn hnpos frames E).nextTarget (residualOrbitRanking hnpos)
      (orbOf s) hcurlt = t := by
    have h1 := DAState.nextTarget_getElem? (residualOrbitRanking hnpos)
      (abst hn hnpos frames E) (orbOf s) hcurlt
    rw [hcursor_s, List.getElem?_eq_getElem hkpref, htdef] at h1
    exact (Option.some.inj h1).symm
  have hrt : r.target = orbitTargetLift hnpos t := by
    rw [hrk, ← htdef]; exact fullTrace_getElem_target_pref hn hnpos s (frames s) hk
  have hrkey : r.key = (residualOrbitRanking hnpos).rank (orbOf s) t := by
    rw [hrk, ← htdef]; exact fullTrace_getElem_key_pref hn hnpos s (frames s) hk
  rcases hheld : E.held r.target with _ | ⟨old, rold⟩
  · -- the target is free: the proposal is accepted
    rw [step_accept hq hsmem hadvc hheld] at h
    have hE' := Option.some.inj h
    have hEs : E'.sources = E.sources := by rw [← hE']
    have hEq : E'.queue = rest := by rw [← hE']
    have hEg : E'.gen = Function.update E.gen s g := by rw [← hE']
    have hEh : E'.held = Function.update E.held r.target (some (s, r)) := by rw [← hE']
    have hEa : E'.assigned = Function.update E.assigned s (some r) := by rw [← hE']
    have habsheld : (abst hn hnpos frames E).held t = none := by
      rw [abst_held, ← hrt, hheld]
      rfl
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro x hx; rw [hEs] at hx; exact hSim.canon x hx
    · intro x hx; rw [hEq] at hx; rw [hEs]; exact hqrest x hx
    · intro x
      rw [hEg]
      by_cases hx : x = s
      · subst x; rw [Function.update_self]; exact hsufg
      · rw [Function.update_of_ne hx]; exact hSim.suffix x
    · intro v x r' hv
      rw [hEh] at hv
      rw [hEs]
      by_cases hvv : v = r.target
      · subst v
        rw [Function.update_self] at hv
        obtain ⟨rfl, rfl⟩ : s = x ∧ r = r' :=
          ⟨congrArg Prod.fst (Option.some.inj hv),
            congrArg Prod.snd (Option.some.inj hv)⟩
        exact hsmem
      · rw [Function.update_of_ne hvv] at hv; exact hSim.held_src v x r' hv
    · intro v x r' hv
      rw [hEh] at hv
      by_cases hvv : v = r.target
      · subst v
        rw [Function.update_self] at hv
        obtain ⟨rfl, rfl⟩ : s = x ∧ r = r' :=
          ⟨congrArg Prod.fst (Option.some.inj hv),
            congrArg Prod.snd (Option.some.inj hv)⟩
        rfl
      · rw [Function.update_of_ne hvv] at hv; exact hSim.held_target v x r' hv
    · intro o x r' hv
      rw [hEh] at hv
      by_cases hvv : orbitTargetLift hnpos o = r.target
      · obtain rfl : o = t := orbitTargetLift_injective hnpos (hvv.trans hrt)
        rw [hvv, Function.update_self] at hv
        obtain ⟨rfl, rfl⟩ : s = x ∧ r = r' :=
          ⟨congrArg Prod.fst (Option.some.inj hv),
            congrArg Prod.snd (Option.some.inj hv)⟩
        exact hrkey
      · rw [Function.update_of_ne hvv] at hv; exact hSim.held_key o x r' hv
    · intro x r' hv
      rw [hEa] at hv
      by_cases hx : x = s
      · subst x
        rw [Function.update_self] at hv
        obtain rfl := Option.some.inj hv
        exact ⟨t, hrt⟩
      · rw [Function.update_of_ne hx] at hv; exact hSim.assigned_lift x r' hv
    · rw [DAState.step_of_queue_cons _ _ (orbOf s) (rest.map orbOf) hqabs hcurlt,
        DAState.advance_of_held_none _ _ (orbOf s) (rest.map orbOf) hcurlt
          (by rw [hnextEq]; exact habsheld)]
      refine congrArg some (DAState.ext' _ ?_ ?_ ?_ ?_)
      · rw [DAState.acceptEmpty_queue, abst_queue, hEq]
      · rw [DAState.acceptEmpty_cursor]
        exact abst_cursor_update hn hnpos frames hcanon hEg hcurg
      · rw [DAState.acceptEmpty_held, hnextEq]
        exact abst_held_update hn hnpos frames hrt hEh
      · rw [DAState.acceptEmpty_assigned, hnextEq]
        exact abst_assigned_update hn hnpos frames hcanon hrt hEa
  · have holdmem : old ∈ E.sources := hSim.held_src _ _ _ hheld
    have hcanonOld : canonicalBResidualRepresentative (orbOf old) = old :=
      hSim.canon old holdmem
    have hroldkey : rold.key = (residualOrbitRanking hnpos).rank (orbOf old) t :=
      hSim.held_key t old rold (by rw [← hrt]; exact hheld)
    have habsheld : (abst hn hnpos frames E).held t = some (orbOf old) := by
      rw [abst_held, ← hrt, hheld]
      rfl
    by_cases hlt : r.key < rold.key
    · -- the proposal displaces the incumbent
      rw [step_replace hq hsmem hadvc hheld hlt] at h
      have hE' := Option.some.inj h
      have hEs : E'.sources = E.sources := by rw [← hE']
      have hEq : E'.queue = rest ++ [old] := by rw [← hE']
      have hEg : E'.gen = Function.update E.gen s g := by rw [← hE']
      have hEh : E'.held = Function.update E.held r.target (some (s, r)) := by rw [← hE']
      have hEa : E'.assigned =
          Function.update (Function.update E.assigned old none) s (some r) := by
        rw [← hE']
      have hbetter : (residualOrbitRanking hnpos).rank (orbOf s) t <
          (residualOrbitRanking hnpos).rank (orbOf old) t := by
        rw [← hrkey, ← hroldkey]; exact hlt
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · intro x hx; rw [hEs] at hx; exact hSim.canon x hx
      · intro x hx
        rw [hEq] at hx
        rw [hEs]
        rcases List.mem_append.mp hx with hx' | hx'
        · exact hqrest x hx'
        · rw [List.mem_singleton.mp hx']; exact holdmem
      · intro x
        rw [hEg]
        by_cases hx : x = s
        · subst x; rw [Function.update_self]; exact hsufg
        · rw [Function.update_of_ne hx]; exact hSim.suffix x
      · intro v x r' hv
        rw [hEh] at hv
        rw [hEs]
        by_cases hvv : v = r.target
        · subst v
          rw [Function.update_self] at hv
          obtain ⟨rfl, rfl⟩ : s = x ∧ r = r' :=
            ⟨congrArg Prod.fst (Option.some.inj hv),
              congrArg Prod.snd (Option.some.inj hv)⟩
          exact hsmem
        · rw [Function.update_of_ne hvv] at hv; exact hSim.held_src v x r' hv
      · intro v x r' hv
        rw [hEh] at hv
        by_cases hvv : v = r.target
        · subst v
          rw [Function.update_self] at hv
          obtain ⟨rfl, rfl⟩ : s = x ∧ r = r' :=
            ⟨congrArg Prod.fst (Option.some.inj hv),
              congrArg Prod.snd (Option.some.inj hv)⟩
          rfl
        · rw [Function.update_of_ne hvv] at hv; exact hSim.held_target v x r' hv
      · intro o x r' hv
        rw [hEh] at hv
        by_cases hvv : orbitTargetLift hnpos o = r.target
        · obtain rfl : o = t := orbitTargetLift_injective hnpos (hvv.trans hrt)
          rw [hvv, Function.update_self] at hv
          obtain ⟨rfl, rfl⟩ : s = x ∧ r = r' :=
            ⟨congrArg Prod.fst (Option.some.inj hv),
              congrArg Prod.snd (Option.some.inj hv)⟩
          exact hrkey
        · rw [Function.update_of_ne hvv] at hv; exact hSim.held_key o x r' hv
      · intro x r' hv
        rw [hEa] at hv
        by_cases hx : x = s
        · subst x
          rw [Function.update_self] at hv
          obtain rfl := Option.some.inj hv
          exact ⟨t, hrt⟩
        · rw [Function.update_of_ne hx] at hv
          by_cases hxo : x = old
          · subst x; rw [Function.update_self] at hv; exact absurd hv (by simp)
          · rw [Function.update_of_ne hxo] at hv; exact hSim.assigned_lift x r' hv
      · rw [DAState.step_of_queue_cons _ _ (orbOf s) (rest.map orbOf) hqabs hcurlt,
          DAState.advance_of_replace _ _ (orbOf s) (rest.map orbOf) hcurlt
            (by rw [hnextEq]; exact habsheld) (by rw [hnextEq]; exact hbetter)]
        refine congrArg some (DAState.ext' _ ?_ ?_ ?_ ?_)
        · rw [DAState.replaceHeld_queue, abst_queue, hEq, List.map_append]
          rfl
        · rw [DAState.replaceHeld_cursor]
          exact abst_cursor_update hn hnpos frames hcanon hEg hcurg
        · rw [DAState.replaceHeld_held, hnextEq]
          exact abst_held_update hn hnpos frames hrt hEh
        · rw [DAState.replaceHeld_assigned, hnextEq]
          exact abst_assigned_update_replace hn hnpos frames hcanon hcanonOld hrt hEa
    · -- the incumbent survives and the proposer is requeued
      rw [step_reject hq hsmem hadvc hheld hlt] at h
      have hE' := Option.some.inj h
      have hEs : E'.sources = E.sources := by rw [← hE']
      have hEq : E'.queue = rest ++ [s] := by rw [← hE']
      have hEg : E'.gen = Function.update E.gen s g := by rw [← hE']
      have hEh : E'.held = E.held := by rw [← hE']
      have hEa : E'.assigned = E.assigned := by rw [← hE']
      have hworse : ¬ (residualOrbitRanking hnpos).rank (orbOf s) t <
          (residualOrbitRanking hnpos).rank (orbOf old) t := by
        rw [← hrkey, ← hroldkey]; exact hlt
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · intro x hx; rw [hEs] at hx; exact hSim.canon x hx
      · intro x hx
        rw [hEq] at hx
        rw [hEs]
        rcases List.mem_append.mp hx with hx' | hx'
        · exact hqrest x hx'
        · rw [List.mem_singleton.mp hx']; exact hsmem
      · intro x
        rw [hEg]
        by_cases hx : x = s
        · subst x; rw [Function.update_self]; exact hsufg
        · rw [Function.update_of_ne hx]; exact hSim.suffix x
      · intro v x r' hv
        rw [hEh] at hv; rw [hEs]; exact hSim.held_src v x r' hv
      · intro v x r' hv
        rw [hEh] at hv; exact hSim.held_target v x r' hv
      · intro o x r' hv
        rw [hEh] at hv; exact hSim.held_key o x r' hv
      · intro x r' hv
        rw [hEa] at hv; exact hSim.assigned_lift x r' hv
      · rw [DAState.step_of_queue_cons _ _ (orbOf s) (rest.map orbOf) hqabs hcurlt,
          DAState.advance_of_reject _ _ (orbOf s) (rest.map orbOf) hcurlt
            (by rw [hnextEq]; exact habsheld) (by rw [hnextEq]; exact hworse)]
        refine congrArg some (DAState.ext' _ ?_ ?_ ?_ ?_)
        · rw [DAState.rejectProposal_queue, abst_queue, hEq, List.map_append]
          rfl
        · rw [DAState.rejectProposal_cursor]
          exact abst_cursor_update hn hnpos frames hcanon hEg hcurg
        · rw [DAState.rejectProposal_held]
          funext o
          rw [abst_held, abst_held, hEh]
        · rw [DAState.rejectProposal_assigned]
          funext q
          rw [abst_assigned, abst_assigned, hEa]
theorem sim_run (hn : Odd n) (hnpos : 0 < n) (frames : FrameFamily n) :
    ∀ {E : DARun n}, Sim hnpos frames E →
      Sim hnpos frames (run frames E) ∧
        abst hn hnpos frames (run frames E) =
          (abst hn hnpos frames E).run (residualOrbitRanking hnpos) := by
  intro E
  induction E using run.induct (frames := frames) with
  | case1 E hstep =>
      intro hSim
      rw [run, hstep]
      dsimp only
      exact ⟨hSim, (DAState.run_of_step_none _ _
        (step_none_sim hn hnpos frames hSim hstep)).symm⟩
  | case2 E E' hstep ih =>
      intro hSim
      obtain ⟨hSim', habs⟩ := step_some_sim hn hnpos frames hSim hstep
      obtain ⟨hs, ha⟩ := ih hSim'
      rw [run, hstep]
      dsimp only
      exact ⟨hs, ha.trans (DAState.run_of_step_some _ _ _ habs).symm⟩
omit [Fintype (BOddRep n)] [Fintype (ARep n)] in
theorem sim_initial (hnpos : 0 < n) (frames : FrameFamily n)
    {roster : List (BResidual n)}
    (hcanon : ∀ x ∈ roster, canonicalBResidualRepresentative (orbOf x) = x) :
    Sim hnpos frames (DARun.initial roster) := by
  refine ⟨hcanon, fun x hx => hx, fun x => ?_, ?_, ?_, ?_, ?_⟩
  · show remainingTrace x (frames x) GenState.initial <:+ fullTrace x (frames x)
    rw [remainingTrace_initial]
  · intro v x r' hv; simp [DARun.initial] at hv
  · intro v x r' hv; simp [DARun.initial] at hv
  · intro o x r' hv; simp [DARun.initial] at hv
  · intro x r' hv; simp [DARun.initial] at hv
theorem abst_initial (hn : Odd n) (hnpos : 0 < n) (frames : FrameFamily n)
    (roster : List (BResidual n)) :
    abst hn hnpos frames (DARun.initial roster) =
      DAState.initial (residualOrbitRanking hnpos) (roster.map orbOf) := by
  refine DAState.ext' _ rfl ?_ rfl rfl
  funext q
  show cursorOf frames (DARun.initial roster) _ = 0
  simp only [cursorOf, DARun.initial, remainingTrace_initial, Nat.sub_self]
noncomputable def sourceRoster (n : ℤ) [Fintype (BOddRep n)] :
    List (BResidual n) :=
  (residualSourceOrder (n := n)).map canonicalBResidualRepresentative
omit [Fintype (ARep n)] in
theorem sourceRoster_canon (x : BResidual n) (hx : x ∈ sourceRoster n) :
    canonicalBResidualRepresentative (orbOf x) = x := by
  obtain ⟨q, -, rfl⟩ := List.mem_map.mp hx
  rw [orbOf_rep]
omit [Fintype (ARep n)] in
theorem sourceRoster_map_orbOf :
    (sourceRoster n).map orbOf = residualSourceOrder := by
  rw [sourceRoster, List.map_map]
  refine Eq.trans (List.map_congr_left ?_) (List.map_id _)
  intro q _
  exact orbOf_rep q
noncomputable def terminalRun (frames : FrameFamily n) : DARun n :=
  run frames (DARun.initial (sourceRoster n))
theorem abst_terminalRun (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n) :
    abst hn hnpos frames (terminalRun frames) =
      (DAState.initial (residualOrbitRanking hnpos)
        (residualSourceOrder (n := n))).run (residualOrbitRanking hnpos) := by
  rw [terminalRun,
    (sim_run hn hnpos frames (sim_initial hnpos frames sourceRoster_canon)).2,
    abst_initial, sourceRoster_map_orbOf]
section Terminal
theorem initial_abst_valid (hnpos : 0 < n) :
    (DAState.initial (residualOrbitRanking hnpos)
        (residualSourceOrder (n := n))).Valid (residualOrbitRanking hnpos) :=
  DAState.initial_valid _ _ residualSourceOrder_nodup mem_residualSourceOrder
theorem valid_abst_terminalRun (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n) :
    (abst hn hnpos frames (terminalRun frames)).Valid
      (residualOrbitRanking hnpos) := by
  rw [abst_terminalRun]
  exact DAState.valid_run _ _ (initial_abst_valid hnpos)
theorem terminalRun_queue_nil (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    (terminalRun frames).queue = [] := by
  have hq : (abst hn hnpos frames (terminalRun frames)).queue = [] := by
    rw [abst_terminalRun]
    exact DAState.run_queue_nil _ hcard _ (initial_abst_valid hnpos)
  rw [abst_queue] at hq
  simpa using hq
noncomputable def runMatching (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    (bResidualInvolution n).Orbit ≃ (aResidualInvolution n hnpos).Orbit :=
  DAState.matchingOfTerminal (residualOrbitRanking hnpos) hcard
    (abst hn hnpos frames (terminalRun frames))
    (valid_abst_terminalRun hn hnpos frames)
    (by
      rw [abst_queue, terminalRun_queue_nil hn hnpos frames hcard]
      rfl)
end Terminal
end RecordDA
end TunnellMap


