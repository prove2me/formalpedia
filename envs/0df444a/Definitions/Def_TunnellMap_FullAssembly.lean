-- Prove2me | Definitions.Def_TunnellMap_FullAssembly
-- name    : TunnellMap_FullAssembly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:50:10.872024+00:00
-- url     : https://prove2.me/theorems/6f290638-b8b7-452b-a094-8dcd2c521a10
-- title:
--   Full Assembly
-- statement:
--   Definitions and structural lemmas for Full Assembly, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FullAssembly.lean

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_Finiteness
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
def BEvenRep (n : ℤ) := {p : BRep n // Even p.1.z}
theorem BEvenParam.extensionality {n : ℤ} {p q : BEvenParam n}
    (hx : p.x = q.x) (hy : p.y = q.y) (hw : p.w = q.w) : p = q := by
  cases p
  cases q
  simp_all
def evenRepToParam {n : ℤ} (p : BEvenRep n) : BEvenParam n := by
  refine ⟨p.1.1.x, p.1.1.y, p.1.1.z / 2, ?_⟩
  have hform := p.1.2
  change bForm ⟨p.1.1.x, p.1.1.y, 2 * (p.1.1.z / 2)⟩ = n
  have hdiv : (2 : ℤ) ∣ p.1.1.z := even_iff_two_dvd.mp p.2
  have hz' : 2 * (p.1.1.z / 2) = p.1.1.z := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel hdiv
  rw [hz']
  exact hform
def evenParamToRep {n : ℤ} (p : BEvenParam n) : BEvenRep n :=
  ⟨p.asBRep, ⟨p.w, by dsimp [BEvenParam.asBRep]; omega⟩⟩
def evenRepParamEquiv (n : ℤ) : BEvenRep n ≃ BEvenParam n := by
  refine
    { toFun := evenRepToParam
      invFun := evenParamToRep
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    apply Subtype.ext
    apply Subtype.ext
    apply Triple.ext
    · rfl
    · rfl
    · change 2 * (p.1.1.z / 2) = p.1.1.z
      rw [mul_comm]
      exact Int.ediv_mul_cancel (even_iff_two_dvd.mp p.2)
  · intro p
    apply BEvenParam.extensionality
    · rfl
    · rfl
    · change (2 * p.w) / 2 = p.w
      exact Int.mul_ediv_cancel_left p.w (by norm_num)
def bOddSubtypeEquiv (n : ℤ) :
    {p : BRep n // Odd p.1.z} ≃ BOddRep n where
  toFun p := ⟨p.1.1, p.1.2, p.2⟩
  invFun p := ⟨⟨p.1, p.2.1⟩, p.2.2⟩
  left_inv := by
    intro p
    rfl
  right_inv := by
    intro p
    rfl
noncomputable def bRepParityEquiv (n : ℤ) :
    BRep n ≃ BEvenParam n ⊕ BOddRep n := by
  classical
  exact (Equiv.sumCompl (fun p : BRep n => Even p.1.z)).symm.trans
    (Equiv.sumCongr (evenRepParamEquiv n)
      ((Equiv.subtypeEquivRight (fun p : BRep n => Int.not_even_iff_odd)).trans
        (bOddSubtypeEquiv n)))
noncomputable instance bOddRepFintype {n : ℤ} [Fintype (BRep n)] :
    Fintype (BOddRep n) := by
  classical
  letI : Fintype {p : BRep n // Odd p.1.z} := Fintype.ofFinite _
  exact Fintype.ofEquiv _ (bOddSubtypeEquiv n)
noncomputable instance bEvenParamFintype {n : ℤ} [Fintype (ARep n)] :
    Fintype (BEvenParam n) := Fintype.ofEquiv _ (evenEquiv n).symm
theorem odd_card_eq_of_full_balance {n : ℤ}
    [Fintype (BRep n)] [Fintype (ARep n)]
    (hbalance : Fintype.card (BRep n) = 2 * Fintype.card (ARep n)) :
    Fintype.card (BOddRep n) = Fintype.card (ARep n) := by
  classical
  have hsplit := Fintype.card_congr (bRepParityEquiv n)
  have heven := Fintype.card_congr (evenEquiv n)
  rw [Fintype.card_sum] at hsplit
  omega
noncomputable def paperOddEquiv {n : ℤ} (hn : Odd n) (hnpos : 0 < n)
    [Fintype (BRep n)] [Fintype (ARep n)]
    (hbalance : Fintype.card (BRep n) = 2 * Fintype.card (ARep n)) :
    BOddRep n ≃ ARep n :=
  oddEquivOfBalance hn hnpos (odd_card_eq_of_full_balance hbalance)
noncomputable def paperTunnellMap {n : ℤ} (hn : Odd n) (hnpos : 0 < n)
    [Fintype (BRep n)] [Fintype (ARep n)]
    (hbalance : Fintype.card (BRep n) = 2 * Fintype.card (ARep n)) :
    BRep n → ARep n := fun p =>
  conditionalTunnellMap (paperOddEquiv hn hnpos hbalance) (bRepParityEquiv n p)
end TunnellMap


