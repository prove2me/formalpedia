-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
-- name    : QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T12:57:58.763861+00:00
-- url     : https://prove2.me/theorems/753bd57e-9017-4315-89c9-143ed8c0b476
-- title:
--   Original Piece Subsum Obstruction
-- statement:
--   Definitions and structural lemmas for Original Piece Subsum Obstruction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_marks_physical
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_uniform_topMarks
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_topMarks_active
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

set_option autoImplicit false
namespace QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators
noncomputable def outputPieceSubsum (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (O : AssemblyStepOutput (indexedDecoderData S depth) i)
    (A : Finset (Fin O.localComponents.length)) : (indexedFamily S depth).Correction i.succ :=
  ∑ a ∈ A, O.componentAt a
noncomputable def topPieceSubsum (S : OddScale) (j : Nat)
    (A : Finset (Fin (topOutput S j).localComponents.length)) :
    (indexedFamily S (2*j+4)).Correction (TopIndex (2*j+4)) :=
  outputPieceSubsum S (2*j+4) ⟨2*j+3, by omega⟩ (topOutput S j) A
noncomputable def canonicalMarks (S : OddScale) (j : Nat) : Finset (UniformNode S j) :=
  BDL26CanonicalHistoryMarks.marks S (2*j+2) (upperSyndrome S j)
theorem canonical_top_iff (S : OddScale) (j : Nat)
    (v : Vertex (state S (2*j+3)).presentation) :
    BDL26UniformTopOwnerIsolation.topNode S (2*j+3) v ∈ canonicalMarks S j ↔
      v ∈ topMarks S j := by
  have hm := BDL26CanonicalHistoryMarks.mem_marks_physical S (2*j+2)
    (upperSyndrome S j) (Fin.last (2*j+2)) v
  have ht := congrArg (fun M : Finset (Vertex (state S (2*j+3)).presentation) => v ∈ M)
    (BDL26CanonicalHistoryMarks.uniform_topMarks S j)
  exact hm.trans ht.to_iff
noncomputable def canonicalLowerMarks (S : OddScale) (j : Nat) :
    Finset (StrictLowerNode S j) :=
  Finset.univ.filter (fun v => includeLowerNode S j v ∈ canonicalMarks S j)
theorem canonical_active (S : OddScale) (j : Nat)
    (p : FamilyZ S (2*j+4) (TopIndex (2*j+4)))
    (hp : (upperSyndrome S j).val p ≠ 0) :
    BDL26UniformTopOwnerIsolation.topNode S (2*j+3) (topOwner S j p) ∈ canonicalMarks S j :=
  (canonical_top_iff S j _).mpr (topMarks_active S j p hp)
noncomputable def canonicalComponent (S : OddScale) (j : Nat)
    (p : FamilyZ S (2*j+4) (TopIndex (2*j+4)))
    (hp : (upperSyndrome S j).val p ≠ 0) : Finset (UniformNode S j) :=
  (BDL26UniformTopOwnerIsolation.markedComponent S (2*j+3) (canonicalMarks S j)
    ⟨BDL26UniformTopOwnerIsolation.topNode S (2*j+3) (topOwner S j p),
      canonical_active S j p hp⟩).image Subtype.val
end QEC.Coding.BDL26OriginalPieceSubsumObstruction


