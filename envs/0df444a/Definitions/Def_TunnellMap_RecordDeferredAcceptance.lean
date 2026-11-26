-- Prove2me | Definitions.Def_TunnellMap_RecordDeferredAcceptance
-- name    : TunnellMap_RecordDeferredAcceptance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T15:31:28.237449+00:00
-- url     : https://prove2.me/theorems/ce0b8957-88cc-5b49-9a65-9d68d16df606
-- title:
--   Record Deferred Acceptance
-- statement:
--   Definitions and structural lemmas for Record Deferred Acceptance, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordDeferredAcceptance.lean

import Definitions.Def_TunnellMap_BlockGeneratorState
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Theorems.Thm_TunnellMap_BlockGen_remainingTrace_initial
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_matchingOfTerminal_apply
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
namespace RecordDA
open OrderedGenerator BlockGen
instance bOddRepDecidableEq (n : ℤ) : DecidableEq (BOddRep n) :=
  inferInstanceAs (DecidableEq {p : Triple // bForm p = n ∧ Odd p.z})
variable {n : ℤ}
abbrev FrameFamily (n : ℤ) :=
  ∀ s : BResidual n, OrthogonalFrame (tau (residualSourceLift s))
structure DARun (n : ℤ) where
  /-- The fixed roster of source representatives. -/
  sources : List (BResidual n)
  /-- The FIFO queue of currently unassigned sources. -/
  queue : List (BResidual n)
  /-- Generator-internal storage: one one-block generator state per source. -/
  gen : BResidual n → GenState
  /-- The record currently held at each target lift, with its proposer. -/
  held : Triple → Option (BResidual n × IncidentRecord)
  /-- The record currently accepted for each source. -/
  assigned : BResidual n → Option IncidentRecord
def DARun.initial (sources : List (BResidual n)) : DARun n where
  sources := sources
  queue := sources
  gen := fun _ => GenState.initial
  held := fun _ => none
  assigned := fun _ => none
def load (frames : FrameFamily n) (E : DARun n) : ℕ :=
  (E.sources.map fun s => (remainingTrace s (frames s) (E.gen s)).length).sum
def step (frames : FrameFamily n) (E : DARun n) : Option (DARun n) :=
  match E.queue with
  | [] => none
  | s :: rest =>
      if s ∈ E.sources then
        match BlockGen.advance s (frames s) (E.gen s) with
        | none => none
        | some (r, g) =>
            match E.held r.target with
            | none =>
                some { E with
                  queue := rest
                  gen := Function.update E.gen s g
                  held := Function.update E.held r.target (some (s, r))
                  assigned := Function.update E.assigned s (some r) }
            | some (old, rold) =>
                if r.key < rold.key then
                  some { E with
                    queue := rest ++ [old]
                    gen := Function.update E.gen s g
                    held := Function.update E.held r.target (some (s, r))
                    assigned := Function.update
                      (Function.update E.assigned old none) s (some r) }
                else
                  some { E with
                    queue := rest ++ [s]
                    gen := Function.update E.gen s g }
      else none
variable {frames : FrameFamily n} {E : DARun n} {s old : BResidual n}
  {rest : List (BResidual n)} {r rold : IncidentRecord} {g : GenState}
theorem step_nil (hq : E.queue = []) : step frames E = none := by
  unfold step; rw [hq]
theorem step_not_source (hq : E.queue = s :: rest) (hs : s ∉ E.sources) :
    step frames E = none := by
  unfold step; rw [hq]; dsimp only; rw [if_neg hs]
theorem step_exhausted (hq : E.queue = s :: rest) (hs : s ∈ E.sources)
    (hadv : BlockGen.advance s (frames s) (E.gen s) = none) :
    step frames E = none := by
  unfold step; rw [hq]; dsimp only; rw [if_pos hs, hadv]
theorem step_accept (hq : E.queue = s :: rest) (hs : s ∈ E.sources)
    (hadv : BlockGen.advance s (frames s) (E.gen s) = some (r, g))
    (hheld : E.held r.target = none) :
    step frames E = some { E with
      queue := rest
      gen := Function.update E.gen s g
      held := Function.update E.held r.target (some (s, r))
      assigned := Function.update E.assigned s (some r) } := by
  unfold step; rw [hq]; dsimp only; rw [if_pos hs, hadv]; dsimp only; rw [hheld]
theorem step_replace (hq : E.queue = s :: rest) (hs : s ∈ E.sources)
    (hadv : BlockGen.advance s (frames s) (E.gen s) = some (r, g))
    (hheld : E.held r.target = some (old, rold)) (hlt : r.key < rold.key) :
    step frames E = some { E with
      queue := rest ++ [old]
      gen := Function.update E.gen s g
      held := Function.update E.held r.target (some (s, r))
      assigned := Function.update
        (Function.update E.assigned old none) s (some r) } := by
  unfold step; rw [hq]; dsimp only; rw [if_pos hs, hadv]; dsimp only
  rw [hheld]; dsimp only; rw [if_pos hlt]
theorem step_reject (hq : E.queue = s :: rest) (hs : s ∈ E.sources)
    (hadv : BlockGen.advance s (frames s) (E.gen s) = some (r, g))
    (hheld : E.held r.target = some (old, rold)) (hlt : ¬ r.key < rold.key) :
    step frames E = some { E with
      queue := rest ++ [s]
      gen := Function.update E.gen s g } := by
  unfold step; rw [hq]; dsimp only; rw [if_pos hs, hadv]; dsimp only
  rw [hheld]; dsimp only; rw [if_neg hlt]
theorem step_shape {E' : DARun n} (h : step frames E = some E') :
    ∃ (s : BResidual n) (rest : List (BResidual n)) (r : IncidentRecord)
      (g : GenState), E.queue = s :: rest ∧ s ∈ E.sources ∧
        BlockGen.advance s (frames s) (E.gen s) = some (r, g) ∧
        E'.sources = E.sources ∧ E'.gen = Function.update E.gen s g := by
  by_cases hq0 : E.queue = []
  · rw [step_nil hq0] at h; exact absurd h (by simp)
  · obtain ⟨s, rest, hq⟩ := List.exists_cons_of_ne_nil hq0
    by_cases hs : s ∈ E.sources
    · cases hadv : BlockGen.advance s (frames s) (E.gen s) with
        | none => rw [step_exhausted hq hs hadv] at h; exact absurd h (by simp)
        | some rg =>
            obtain ⟨r, g⟩ := rg
            refine ⟨s, rest, r, g, hq, hs, hadv, ?_⟩
            cases hheld : E.held r.target with
            | none =>
                rw [step_accept hq hs hadv hheld] at h
                obtain rfl := Option.some.inj h
                exact ⟨rfl, rfl⟩
            | some p =>
                obtain ⟨o, ro⟩ := p
                by_cases hlt : r.key < ro.key
                · rw [step_replace hq hs hadv hheld hlt] at h
                  obtain rfl := Option.some.inj h
                  exact ⟨rfl, rfl⟩
                · rw [step_reject hq hs hadv hheld hlt] at h
                  obtain rfl := Option.some.inj h
                  exact ⟨rfl, rfl⟩
    · rw [step_not_source hq hs] at h; exact absurd h (by simp)
theorem sum_map_lt_of_mem {α : Type*} (l : List α) (f gf : α → ℕ) (a : α)
    (ha : a ∈ l) (hle : ∀ x, gf x ≤ f x) (hlt : gf a < f a) :
    (l.map gf).sum < (l.map f).sum := by
  induction l with
  | nil => cases ha
  | cons b t ih =>
      rcases List.mem_cons.mp ha with rfl | hmem
      · have hsum : (t.map gf).sum ≤ (t.map f).sum := by
          clear ih ha
          induction t with
          | nil => simp
          | cons c u ihu => simpa using Nat.add_le_add (hle c) ihu
        simpa using Nat.add_lt_add_of_lt_of_le hlt hsum
      · exact Nat.add_lt_add_of_le_of_lt (hle b) (ih hmem)
theorem load_lt (frames : FrameFamily n) {E E' : DARun n}
    (h : step frames E = some E') : load frames E' < load frames E := by
  obtain ⟨s, rest, r, g, hq, hs, hadv, hsrc, hgen⟩ := step_shape h
  unfold load
  rw [hsrc, hgen]
  refine sum_map_lt_of_mem _ _ _ s hs ?_ ?_
  · intro x
    by_cases hx : x = s
    · subst x
      rw [Function.update_self, advance_eq_some (frames s) hadv]
      simp
    · rw [Function.update_of_ne hx]
  · rw [Function.update_self, advance_eq_some (frames s) hadv]
    simp
def run (frames : FrameFamily n) (E : DARun n) : DARun n :=
  match _hstep : step frames E with
  | none => E
  | some E' => run frames E'
termination_by load frames E
decreasing_by exact load_lt frames _hstep
def OneBlockAll (frames : FrameFamily n) (E : DARun n) : Prop :=
  ∀ s : BResidual n, OneBlock s (frames s) (E.gen s)
end RecordDA
end TunnellMap


