-- Prove2me | Definitions.Def_TunnellMap_BlockGenerator
-- name    : TunnellMap_BlockGenerator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:55:05.955844+00:00
-- url     : https://prove2.me/theorems/a1079e02-3743-51f3-a4e8-fc7d5b8de539
-- title:
--   Block Generator
-- statement:
--   Definitions and structural lemmas for Block Generator, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGenerator.lean

import Definitions.Def_TunnellMap_OrderedGenerator
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_ResidualTargetTest
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
structure IncidentRecord where
  key : DirectionKey
  target : Triple
  sign : ℤ
deriving DecidableEq
variable {n : ℤ} {p : Triple}
def hMax (n : ℤ) : ℤ := (n - 1) / 2
def blockIndexList (n : ℤ) (F : OrthogonalFrame p) (h : ℤ) : List GeneratorIndex :=
  ((qValues n h).sort (· ≤ ·)).flatMap fun q =>
    ((bValues n F h q).sort (· ≤ ·)).flatMap fun b =>
      ((rootValues F h q b).sort (· ≤ ·)).map fun u => ⟨h, q, b, u⟩
def Retained (s : BResidual n) (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : GeneratorIndex) : Prop :=
  InTauLattice (rValue F i) ∧
    tripleGcd (dValue F i) = 1 ∧
    FirstNonzeroPositive (dValue F i) ∧
    Odd (dValue F i).z ∧
    IsResidualTargetLift n (targetValue s F i) ∧
    primitiveKey (dValue F i) <
      directionKeyExec (vsub (residualSourceLift s) (targetValue s F i))
def retainedB (s : BResidual n) (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : GeneratorIndex) : Bool :=
  decide (InTauLattice (rValue F i)) &&
  decide (tripleGcd (dValue F i) = 1) &&
  decide (FirstNonzeroPositive (dValue F i)) &&
  decide (Odd (dValue F i).z) &&
  decide (IsResidualTargetLift n (targetValue s F i)) &&
  keyLtExec (primitiveKey (dValue F i))
    (directionKeyExec (vsub (residualSourceLift s) (targetValue s F i)))
theorem retainedB_iff (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) (i : GeneratorIndex) :
    retainedB s F i = true ↔ Retained s F i := by
  simp only [retainedB, Retained, Bool.and_eq_true, decide_eq_true_eq, keyLtExec_iff,
    and_assoc]
instance retainedDecidable (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) (i : GeneratorIndex) :
    Decidable (Retained s F i) :=
  decidable_of_iff _ (retainedB_iff s F i)
def recordOf (s : BResidual n) (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : GeneratorIndex) : IncidentRecord :=
  ⟨primitiveKey (dValue F i), canonicalTargetLift (targetValue s F i),
    targetLiftSign (targetValue s F i)⟩
def emit (s : BResidual n) (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : GeneratorIndex) : Option IncidentRecord :=
  if Retained s F i then some (recordOf s F i) else none
def recordLe (r₁ r₂ : IncidentRecord) : Bool := keyLeExec r₁.key r₂.key
def blockRecords (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) (h : ℤ) :
    List IncidentRecord :=
  ((blockIndexList n F h).filterMap (emit s F)).mergeSort recordLe
def blocksFrom (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) (h : ℤ) :
    List IncidentRecord :=
  if h ≤ hMax n then blockRecords s F h ++ blocksFrom s F (h + 1) else []
termination_by (hMax n + 1 - h).toNat
decreasing_by omega
structure GenState where
  nextBlock : ℤ
  pending : List IncidentRecord
deriving DecidableEq
def GenState.initial : GenState := ⟨1, []⟩
def advance (s : BResidual n) (F : OrthogonalFrame (tau (residualSourceLift s)))
    (st : GenState) : Option (IncidentRecord × GenState) :=
  match st with
  | ⟨h, r :: rest⟩ => some (r, ⟨h, rest⟩)
  | ⟨h, []⟩ =>
      if h ≤ hMax n then advance s F ⟨h + 1, blockRecords s F h⟩ else none
termination_by (hMax n + 1 - st.nextBlock).toNat
decreasing_by omega
def remainingTrace (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) (st : GenState) :
    List IncidentRecord :=
  st.pending ++ blocksFrom s F st.nextBlock
def fullTrace (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) : List IncidentRecord :=
  blocksFrom s F 1
end BlockGen
end TunnellMap


