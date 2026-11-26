-- Prove2me | Definitions.Def_TunnellMap_OrbitLift
-- name    : TunnellMap_OrbitLift
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:44:41.591285+00:00
-- url     : https://prove2.me/theorems/a9c4cc2e-780d-48f9-b785-1580ca877163
-- title:
--   Orbit Lift
-- statement:
--   Definitions and structural lemmas for Orbit Lift, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrbitLift.lean

import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_Assembly
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
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
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_source
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_target
import Theorems.Thm_TunnellMap_residualSourceLift_neg
import Theorems.Thm_TunnellMap_residualTargetLift_neg
import Theorems.Thm_TunnellMap_residual_orbit_card_eq
import Theorems.Thm_TunnellMap_tripleContent_negTriple
import Theorems.Thm_TunnellMap_tripleContent_orientDirection
import Theorems.Thm_TunnellMap_tripleContent_primitiveDirection
import Theorems.Thm_TunnellMap_tripleContent_primitivePartTriple
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_one
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_two
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_zero
import Theorems.Thm_TunnellMap_triplePolynomial_negTriple
import Theorems.Thm_TunnellMap_triplePolynomial_vsmul
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right
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
namespace FreeInvolution
variable {X Y : Type*} (I : FreeInvolution X) (J : FreeInvolution Y)
def signedOrbitProductEquiv (M : I.Orbit ≃ J.Orbit)
    (sign : ∀ _q : I.Orbit, Bool ≃ Bool) :
    I.Orbit × Bool ≃ J.Orbit × Bool where
  toFun qb := ⟨M qb.1, sign qb.1 qb.2⟩
  invFun rb := ⟨M.symm rb.1, (sign (M.symm rb.1)).symm rb.2⟩
  left_inv := by
    intro qb
    rcases qb with ⟨q, b⟩
    simp
  right_inv := by
    intro rb
    rcases rb with ⟨r, b⟩
    simp
section Finite
variable [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
noncomputable def liftOrbitEquiv (M : I.Orbit ≃ J.Orbit)
    (sign : ∀ _q : I.Orbit, Bool ≃ Bool) : X ≃ Y :=
  I.orbitBoolEquiv.trans
    ((I.signedOrbitProductEquiv J M sign).trans J.orbitBoolEquiv.symm)
end Finite
end FreeInvolution
def boolFlipEquiv : Bool ≃ Bool where
  toFun b := !b
  invFun b := !b
  left_inv := by intro b; cases b <;> rfl
  right_inv := by intro b; cases b <;> rfl
noncomputable def orbitSignEquiv {n : ℤ} (hnpos : 0 < n)
    (s : (bResidualInvolution n).Orbit)
    (t : (aResidualInvolution n hnpos).Orbit) : Bool ≃ Bool :=
  if directionKey
      (plusVector ((bResidualInvolution n).representative s)
        ((aResidualInvolution n hnpos).representative t)) <
      directionKey
      (minusVector ((bResidualInvolution n).representative s)
        ((aResidualInvolution n hnpos).representative t)) then
    Equiv.refl Bool
  else
    boolFlipEquiv
noncomputable def preferredTarget {n : ℤ} (s : BResidual n) (t : AResidual n) :
    AResidual n :=
  if directionKey (plusVector s t) < directionKey (minusVector s t) then
    t
  else
    negAResidual t
noncomputable def residualEquivOfOrbitCard {n : ℤ} (hnpos : 0 < n)
    [Fintype (BOddRep n)] [Fintype (ARep n)]
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    BResidual n ≃ AResidual n := by
  classical
  let BI := bResidualInvolution n
  let AI := aResidualInvolution n hnpos
  let M : BI.Orbit ≃ AI.Orbit := residualOrbitMatching hnpos hcard
  exact BI.liftOrbitEquiv AI M (fun s => orbitSignEquiv hnpos s (M s))
noncomputable def oddEquivOfBalance {n : ℤ} (hn : Odd n) (hnpos : 0 < n)
    [Fintype (BOddRep n)] [Fintype (ARep n)]
    (hbalance : Fintype.card (BOddRep n) = Fintype.card (ARep n)) :
    BOddRep n ≃ ARep n := by
  classical
  have horbit := residual_orbit_card_eq hn hnpos hbalance
  let residual : BResidual n ≃ AResidual n := residualEquivOfOrbitCard hnpos horbit
  exact (Equiv.sumCompl DirectSourceUsed).symm.trans
    ((Equiv.sumCongr (directSubsetEquiv hn) residual).trans
      (Equiv.sumCompl DirectTargetUsed))
end TunnellMap


