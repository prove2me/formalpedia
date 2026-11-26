-- Prove2me | Definitions.Def_TunnellMap_ResidualDeferredAcceptance
-- name    : TunnellMap_ResidualDeferredAcceptance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:54:58.481801+00:00
-- url     : https://prove2.me/theorems/33a66b69-9116-5b4b-8853-0d18b509b274
-- title:
--   Residual Deferred Acceptance
-- statement:
--   Definitions and structural lemmas for Residual Deferred Acceptance, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualDeferredAcceptance.lean

import Definitions.Def_TunnellMap_OrderedGenerator
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_OrbitLift
import Theorems.Thm_TunnellMap_FreeInvolution_orbit_canonicalRepresentative
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
import Theorems.Thm_TunnellMap_minusVector_neg_source
import Theorems.Thm_TunnellMap_minusVector_neg_target
import Theorems.Thm_TunnellMap_orthogonalFrame_exists_of_squarefree_norm
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
open OrderedGenerator
section SourceOrder
variable {n : ℤ} [Fintype (BOddRep n)]
def residualSourceOrbitKey
    (s : (bResidualInvolution n).Orbit) : TripleLexKey :=
  bResidualLexKey (canonicalBResidualRepresentative s)
theorem residualSourceOrbitKey_injective :
    Function.Injective (residualSourceOrbitKey (n := n)) := by
  intro s₁ s₂ hkey
  have hrep : canonicalBResidualRepresentative s₁ =
      canonicalBResidualRepresentative s₂ :=
    bResidualLexKey_injective hkey
  let BI := bResidualInvolution n
  calc
    s₁ = BI.orbit (canonicalBResidualRepresentative s₁) :=
      (BI.orbit_canonicalRepresentative bResidualLexKey
        bResidualLexKey_injective s₁).symm
    _ = BI.orbit (canonicalBResidualRepresentative s₂) := by rw [hrep]
    _ = s₂ := BI.orbit_canonicalRepresentative bResidualLexKey
      bResidualLexKey_injective s₂
noncomputable def residualSourceOrder :
    List (bResidualInvolution n).Orbit := by
  classical
  letI : LinearOrder (bResidualInvolution n).Orbit :=
    LinearOrder.lift' residualSourceOrbitKey residualSourceOrbitKey_injective
  exact (Finset.univ : Finset (bResidualInvolution n).Orbit).sort
theorem residualSourceOrder_nodup :
    (residualSourceOrder (n := n)).Nodup := by
  classical
  unfold residualSourceOrder
  exact Finset.sort_nodup _ _
@[simp] theorem mem_residualSourceOrder
    (s : (bResidualInvolution n).Orbit) :
    s ∈ residualSourceOrder (n := n) := by
  classical
  simp [residualSourceOrder]
end SourceOrder
section GeneratedPreferences
variable {n : ℤ} [Fintype (BOddRep n)] [Fintype (ARep n)]
noncomputable def residualSourceFrame (hsquarefree : Squarefree n)
    (s : BResidual n) :
    OrthogonalFrame (tau (residualSourceLift s)) := by
  have hnorm : dot (tau (residualSourceLift s))
      (tau (residualSourceLift s)) = n := by
    rw [qForm_tau]
    simp [residualSourceLift]
  exact Classical.choice
    (orthogonalFrame_exists_of_squarefree_norm hsquarefree hnorm)
end GeneratedPreferences
section AlgorithmicMatching
variable {n : ℤ} (hnpos : 0 < n)
  [Fintype (BOddRep n)] [Fintype (ARep n)]
noncomputable def algorithmicResidualOrbitMatching
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    (bResidualInvolution n).Orbit ≃
      (aResidualInvolution n hnpos).Orbit := by
  classical
  exact GloballyRanked.DAState.deferredAcceptanceMatching
    (residualOrbitRanking hnpos) hcard residualSourceOrder
      residualSourceOrder_nodup mem_residualSourceOrder
noncomputable def algorithmicResidualEquiv
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    BResidual n ≃ AResidual n := by
  classical
  let BI := bResidualInvolution n
  let AI := aResidualInvolution n hnpos
  let M := algorithmicResidualOrbitMatching hnpos hcard
  exact BI.liftOrbitEquiv AI M (fun s => orbitSignEquiv hnpos s (M s))
end AlgorithmicMatching
end TunnellMap


