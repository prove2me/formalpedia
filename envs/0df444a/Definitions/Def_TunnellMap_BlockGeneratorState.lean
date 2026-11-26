-- Prove2me | Definitions.Def_TunnellMap_BlockGeneratorState
-- name    : TunnellMap_BlockGeneratorState
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T15:30:38.081706+00:00
-- url     : https://prove2.me/theorems/6075d5c9-d947-4f59-bf2f-d2abd123d72e
-- title:
--   Block Generator State
-- statement:
--   Definitions and structural lemmas for Block Generator State, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorState.lean

import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Theorems.Thm_TunnellMap_BlockGen_remainingTrace_initial
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
namespace BlockGen
open OrderedGenerator
variable {n : ℤ} {s : BResidual n}
theorem advance_step (F : OrthogonalFrame (tau (residualSourceLift s)))
    (st : GenState) :
    (∀ r st', advance s F st = some (r, st') →
        remainingTrace s F st = r :: remainingTrace s F st') ∧
      (advance s F st = none → remainingTrace s F st = []) := by
  suffices H : ∀ k : ℕ, ∀ st : GenState, (hMax n + 1 - st.nextBlock).toNat = k →
      (∀ r st', advance s F st = some (r, st') →
          remainingTrace s F st = r :: remainingTrace s F st') ∧
        (advance s F st = none → remainingTrace s F st = []) from H _ st rfl
  intro k
  induction k with
  | zero =>
      intro st hk
      obtain ⟨h, pending⟩ := st
      dsimp only at hk
      have hgt : ¬ h ≤ hMax n := by omega
      cases pending with
      | cons r rest =>
          refine ⟨?_, ?_⟩
          · intro r' st' heq
            rw [advance] at heq
            simp only [Option.some.injEq, Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            simp [remainingTrace]
          · intro hnone
            rw [advance] at hnone
            simp at hnone
      | nil =>
          refine ⟨?_, ?_⟩
          · intro r' st' heq
            rw [advance, if_neg hgt] at heq
            simp at heq
          · intro _
            simp only [remainingTrace, List.nil_append]
            rw [blocksFrom, if_neg hgt]
  | succ k ih =>
      intro st hk
      obtain ⟨h, pending⟩ := st
      dsimp only at hk
      cases pending with
      | cons r rest =>
          refine ⟨?_, ?_⟩
          · intro r' st' heq
            rw [advance] at heq
            simp only [Option.some.injEq, Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            simp [remainingTrace]
          · intro hnone
            rw [advance] at hnone
            simp at hnone
      | nil =>
          have hle : h ≤ hMax n := by omega
          have hadv : advance s F ⟨h, []⟩ =
              advance s F ⟨h + 1, blockRecords s F h⟩ := by
            rw [advance, if_pos hle]
          have hrem : remainingTrace s F ⟨h, []⟩ =
              remainingTrace s F ⟨h + 1, blockRecords s F h⟩ := by
            simp only [remainingTrace, List.nil_append]
            rw [blocksFrom, if_pos hle]
          have hih := ih ⟨h + 1, blockRecords s F h⟩ (by dsimp only; omega)
          rw [hadv, hrem]
          exact hih
theorem advance_eq_some (F : OrthogonalFrame (tau (residualSourceLift s)))
    {st : GenState} {r : IncidentRecord} {st' : GenState}
    (h : advance s F st = some (r, st')) :
    remainingTrace s F st = r :: remainingTrace s F st' :=
  (advance_step F st).1 r st' h
theorem advance_length_lt (F : OrthogonalFrame (tau (residualSourceLift s)))
    {st : GenState} {r : IncidentRecord} {st' : GenState}
    (h : advance s F st = some (r, st')) :
    (remainingTrace s F st').length < (remainingTrace s F st).length := by
  rw [advance_eq_some F h]
  simp
def drain (s : BResidual n) (F : OrthogonalFrame (tau (residualSourceLift s)))
    (st : GenState) : List IncidentRecord :=
  match _hadv : advance s F st with
  | none => []
  | some (r, st') => r :: drain s F st'
termination_by (remainingTrace s F st).length
decreasing_by exact advance_length_lt F _hadv
def OneBlock (s : BResidual n) (F : OrthogonalFrame (tau (residualSourceLift s)))
    (st : GenState) : Prop :=
  st.pending <:+ blockRecords s F (st.nextBlock - 1)
end BlockGen
end TunnellMap


