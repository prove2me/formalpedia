-- Prove2me | Definitions.Def_TunnellMap_Examples41Residual
-- name    : TunnellMap_Examples41Residual
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T15:21:36.022359+00:00
-- url     : https://prove2.me/theorems/bc399703-bd02-5662-a4ce-a87a202aa841
-- title:
--   Examples41 Residual
-- statement:
--   Definitions and structural lemmas for Examples41 Residual, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean

import Definitions.Def_TunnellMap_Examples41
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_matchingOfTerminal_apply
import Theorems.Thm_TunnellMap_GloballyRanked_finalPartner_mem_proposalTargets
import Theorems.Thm_TunnellMap_GloballyRanked_get_preferenceIndex
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
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_one
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_two
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_zero
import Theorems.Thm_TunnellMap_triplePolynomial_negTriple
import Theorems.Thm_TunnellMap_triplePolynomial_vsmul
attribute [local simp] TunnellMap.GloballyRanked.DAState.matchingOfTerminal_apply
attribute [local simp] TunnellMap.GloballyRanked.finalPartner_mem_proposalTargets
attribute [local simp] TunnellMap.GloballyRanked.get_preferenceIndex
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
attribute [local simp] TunnellMap.triplePolynomial_coeff_one
attribute [local simp] TunnellMap.triplePolynomial_coeff_two
attribute [local simp] TunnellMap.triplePolynomial_coeff_zero
attribute [local simp] TunnellMap.triplePolynomial_negTriple
attribute [local simp] TunnellMap.triplePolynomial_vsmul


set_option autoImplicit true
namespace TunnellMap
namespace Examples41
set_option maxRecDepth 10000
def s1 : BResidual 41 := by
  refine ⟨⟨⟨-2, -5, -1⟩, by norm_num [bForm], by norm_num⟩, ?_⟩
  simp only [DirectSourceUsed, DirectPredicate1, DirectPredicate2, DirectPredicate3]
  push Not
  constructor
  · intro q
    omega
  · constructor
    · intro q
      omega
    · intro q
      omega
def s2 : BResidual 41 := by
  refine ⟨midpointSource, ?_⟩
  simp only [DirectSourceUsed, DirectPredicate1, DirectPredicate2, DirectPredicate3]
  push Not
  constructor
  · intro q
    simp only [midpointSource]
    omega
  · constructor
    · intro q
      simp only [midpointSource]
      omega
    · intro q
      simp only [midpointSource]
      omega
def s3 : BResidual 41 := by
  refine ⟨⟨⟨-2, 5, -1⟩, by norm_num [bForm], by norm_num⟩, ?_⟩
  simp only [DirectSourceUsed, DirectPredicate1, DirectPredicate2, DirectPredicate3]
  push Not
  constructor
  · intro q
    omega
  · constructor
    · intro q
      omega
    · intro q
      omega
def s4 : BResidual 41 := by
  refine ⟨⟨⟨-2, 5, 1⟩, by norm_num [bForm], by norm_num⟩, ?_⟩
  simp only [DirectSourceUsed, DirectPredicate1, DirectPredicate2, DirectPredicate3]
  push Not
  constructor
  · intro q
    omega
  · constructor
    · intro q
      omega
    · intro q
      omega
def t1 : AResidual 41 := by
  refine ⟨⟨⟨-4, -3, 0⟩, by norm_num [aForm]⟩, ?_⟩
  simp only [DirectTargetUsed, ImagePredicate1, ImagePredicate2, ImagePredicate3]
  push Not
  constructor
  · intro q hq
    rcases hq with ⟨k, hk⟩
    norm_num at hk ⊢
    omega
  · constructor
    · intro q hq
      rcases hq with ⟨k, hk⟩
      norm_num at hk ⊢
      omega
    · intro q hq
      rcases hq with ⟨k, hk⟩
      norm_num at hk ⊢
      omega
def t2 : AResidual 41 := by
  refine ⟨⟨⟨-4, 3, 0⟩, by norm_num [aForm]⟩, ?_⟩
  simp only [DirectTargetUsed, ImagePredicate1, ImagePredicate2, ImagePredicate3]
  push Not
  constructor
  · intro q hq
    rcases hq with ⟨k, hk⟩
    norm_num at hk ⊢
    omega
  · constructor
    · intro q hq
      rcases hq with ⟨k, hk⟩
      norm_num at hk ⊢
      omega
    · intro q hq
      rcases hq with ⟨k, hk⟩
      norm_num at hk ⊢
      omega
def t3 : AResidual 41 := by
  refine ⟨⟨⟨0, -3, -1⟩, by norm_num [aForm]⟩, ?_⟩
  simp only [DirectTargetUsed, ImagePredicate1, ImagePredicate2, ImagePredicate3]
  push Not
  constructor
  · intro q hq
    rcases hq with ⟨k, hk⟩
    norm_num at hk ⊢
    omega
  · constructor
    · intro q hq
      rcases hq with ⟨k, hk⟩
      norm_num at hk ⊢
      omega
    · intro q hq
      rcases hq with ⟨k, hk⟩
      norm_num at hk ⊢
      omega
def t4 : AResidual 41 := by
  refine ⟨⟨⟨0, -3, 1⟩, by norm_num [aForm]⟩, ?_⟩
  simp only [DirectTargetUsed, ImagePredicate1, ImagePredicate2, ImagePredicate3]
  push Not
  constructor
  · intro q hq
    rcases hq with ⟨k, hk⟩
    norm_num at hk ⊢
    omega
  · constructor
    · intro q hq
      rcases hq with ⟨k, hk⟩
      norm_num at hk ⊢
      omega
    · intro q hq
      rcases hq with ⟨k, hk⟩
      norm_num at hk ⊢
      omega
def key41 (h x y z : ℤ) : DirectionKey := ⟨h, x, y, z⟩
end Examples41
end TunnellMap


