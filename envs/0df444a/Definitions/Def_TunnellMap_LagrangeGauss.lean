-- Prove2me | Definitions.Def_TunnellMap_LagrangeGauss
-- name    : TunnellMap_LagrangeGauss
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:54:55.125561+00:00
-- url     : https://prove2.me/theorems/f81a727e-5cab-5807-a54a-b95ef27e25a4
-- title:
--   Lagrange Gauss
-- statement:
--   Definitions and structural lemmas for Lagrange Gauss, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Theorems.Thm_P2M_TunnellMap_orthogonalFrameExec_e__5f3ec14b19af
import Theorems.Thm_P2M_TunnellMap_orthogonalFrameExec_e__63bfe0839bbf
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
import Theorems.Thm_TunnellMap_orthogonalFrameExec_z
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
attribute [local simp] P2M_TunnellMap_orthogonalFrameExec_e__5f3ec14b19af
attribute [local simp] P2M_TunnellMap_orthogonalFrameExec_e__63bfe0839bbf
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
attribute [local simp] TunnellMap.orthogonalFrameExec_z
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
open OrderedGenerator
theorem dot_self_nonneg (v : Triple) : 0 ≤ dot v v := by
  simp only [dot]
  nlinarith [mul_self_nonneg v.x, mul_self_nonneg v.y, mul_self_nonneg v.z]
@[simp] theorem dot_negTriple_left (u v : Triple) :
    dot (negTriple u) v = - dot u v := by simp only [dot, negTriple]; ring
@[simp] theorem dot_negTriple_right (u v : Triple) :
    dot u (negTriple v) = - dot u v := by simp only [dot, negTriple]; ring
theorem cross_vsub_vsmul (u v : Triple) (q : ℤ) :
    cross u (vsub v (vsmul q u)) = cross u v := by
  apply Triple.ext <;> simp only [cross, vsub, vsmul] <;> ring
theorem cross_swap_neg (u v : Triple) : cross v (negTriple u) = cross u v := by
  apply Triple.ext <;> simp only [cross, negTriple] <;> ring
theorem cross_neg_neg (u v : Triple) :
    cross (negTriple u) (negTriple v) = cross u v := by
  apply Triple.ext <;> simp only [cross, negTriple] <;> ring
def nearestQuot (b a : ℤ) : ℤ :=
  if 0 ≤ b then (2 * b + a - 1) / (2 * a) else -((-(2 * b) + a - 1) / (2 * a))
def lgQuot (u v : Triple) : ℤ := nearestQuot (dot u v) (dot u u)
def lgNext (u v : Triple) : Triple := vsub v (vsmul (lgQuot u v) u)
def lgReduceAux (u v : Triple) : Triple × Triple :=
  if _h : dot (lgNext u v) (lgNext u v) < dot u u then
    lgReduceAux (lgNext u v) (negTriple u)
  else (u, lgNext u v)
termination_by (dot u u).toNat
decreasing_by
  have hnn := dot_self_nonneg (lgNext u v)
  omega
def lgNormalize (uv : Triple × Triple) : Triple × Triple :=
  if tripleLexLtExec uv.1 (negTriple uv.1) then
    (negTriple uv.1, negTriple uv.2)
  else uv
def lgSwap (uv : Triple × Triple) : Triple × Triple := (uv.2, negTriple uv.1)
def pairLexLtExec (uv wz : Triple × Triple) : Bool :=
  tripleLexLtExec uv.1 wz.1 ||
    (decide (uv.1 = wz.1) && tripleLexLtExec uv.2 wz.2)
def lgSelect (uv : Triple × Triple) : Triple × Triple :=
  if decide (dot uv.1 uv.1 = dot uv.2 uv.2) &&
      pairLexLtExec (lgNormalize (lgSwap uv)) (lgNormalize uv) then
    lgNormalize (lgSwap uv)
  else lgNormalize uv
def lgReduce (u v : Triple) : Triple × Triple := lgSelect (lgReduceAux u v)
theorem lgReduceAux_cross (u v : Triple) :
    cross (lgReduceAux u v).1 (lgReduceAux u v).2 = cross u v := by
  induction u, v using lgReduceAux.induct with
  | case1 u v h ih =>
      rw [lgReduceAux, dif_pos h, ih, cross_swap_neg, lgNext, cross_vsub_vsmul]
  | case2 u v h =>
      rw [lgReduceAux, dif_neg h]
      show cross u (lgNext u v) = cross u v
      rw [lgNext, cross_vsub_vsmul]
theorem lgNormalize_cross (uv : Triple × Triple) :
    cross (lgNormalize uv).1 (lgNormalize uv).2 = cross uv.1 uv.2 := by
  unfold lgNormalize
  split
  · exact cross_neg_neg _ _
  · rfl
theorem lgSwap_cross (uv : Triple × Triple) :
    cross (lgSwap uv).1 (lgSwap uv).2 = cross uv.1 uv.2 :=
  cross_swap_neg uv.1 uv.2
theorem lgSelect_cross (uv : Triple × Triple) :
    cross (lgSelect uv).1 (lgSelect uv).2 = cross uv.1 uv.2 := by
  unfold lgSelect
  split
  · rw [lgNormalize_cross, lgSwap_cross]
  · exact lgNormalize_cross uv
theorem lgReduce_cross (u v : Triple) :
    cross (lgReduce u v).1 (lgReduce u v).2 = cross u v := by
  rw [lgReduce, lgSelect_cross, lgReduceAux_cross]
def IsReducedPair (uv : Triple × Triple) : Prop :=
  |2 * dot uv.1 uv.2| ≤ dot uv.1 uv.1 ∧ dot uv.1 uv.1 ≤ dot uv.2 uv.2
variable {p : Triple}
def reduceFrame (F : OrthogonalFrame p) : OrthogonalFrame p where
  e₁ := (lgReduce F.e₁ F.e₂).1
  e₂ := (lgReduce F.e₁ F.e₂).2
  z := F.z
  cross_eq := by rw [lgReduce_cross]; exact F.cross_eq
  bezout := F.bezout
end TunnellMap


