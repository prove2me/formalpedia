-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
-- name    : QEC_Coding_FiberBundle_TwistGraph
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:39:46.751204+00:00
-- url     : https://prove2.me/theorems/6ecf254a-aadf-4dec-a23b-ceb9e957fa8f
-- title:
--   Twist Graph
-- statement:
--   Definitions and structural lemmas for Twist Graph, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean

import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomTwist_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_multipleRotation_val
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.independentProduct_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomTwist.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.multipleRotation_val
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
namespace QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
def scaleIntHom (ell : Nat) [NeZero ell] :
    ℤ →+ ZMod (ell * ell) where
  toFun z := (z : ZMod (ell * ell)) * (ell : Nat)
  map_zero' := by simp
  map_add' x y := by
    push_cast
    ring
theorem scaleIntHom_ell_eq_zero (ell : Nat) [NeZero ell] :
    scaleIntHom ell ell = 0 := by
  simp only [scaleIntHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Int.cast_natCast]
  rw [← Nat.cast_mul, ZMod.natCast_self]
def layerEmbedding (ell : Nat) [NeZero ell] :
    ZMod ell →+ ZMod (ell * ell) :=
  ZMod.lift ell ⟨scaleIntHom ell, scaleIntHom_ell_eq_zero ell⟩
@[simp]
theorem layerEmbedding_natCast
    (ell k : Nat) [NeZero ell] :
    layerEmbedding ell (k : ZMod ell) =
      (k * ell : Nat) := by
  rw [show (k : ZMod ell) = ((k : ℤ) : ZMod ell) by norm_num]
  rw [layerEmbedding, ZMod.lift_coe]
  simp only [scaleIntHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Int.cast_natCast, Nat.cast_mul]
@[simp]
theorem layerEmbedding_eq_val_mul
    (ell : Nat) [NeZero ell] (u : ZMod ell) :
    layerEmbedding ell u =
      (u.val * ell : Nat) := by
  calc
    layerEmbedding ell u =
        layerEmbedding ell (u.val : ZMod ell) := by
          rw [ZMod.natCast_zmod_val]
    _ = (u.val * ell : Nat) :=
      layerEmbedding_natCast ell u.val
def blockPosition
    (ell : Nat) [NeZero ell]
    (uk : ZMod ell × Fin ell) : ZMod (ell * ell) :=
  layerEmbedding ell uk.1 + (uk.2.val : Nat)
@[simp]
theorem blockPosition_val
    (ell : Nat) [NeZero ell]
    (u : ZMod ell) (k : Fin ell) :
    (blockPosition ell (u, k)).val = u.val * ell + k.val := by
  have hell : 0 < ell := NeZero.pos ell
  have huBound : u.val * ell < ell * ell := by
    nlinarith [u.val_lt]
  have hkBound : k.val < ell * ell := by
    nlinarith [k.isLt]
  have hsum : u.val * ell + k.val < ell * ell := by
    nlinarith [u.val_lt, k.isLt]
  rw [blockPosition, layerEmbedding_eq_val_mul, ZMod.val_add,
    ZMod.val_natCast_of_lt huBound, ZMod.val_natCast_of_lt hkBound,
    Nat.mod_eq_of_lt hsum]
theorem blockPosition_injective
    (ell : Nat) [NeZero ell] :
    Function.Injective (blockPosition ell) := by
  rintro ⟨u, k⟩ ⟨v, l⟩ huv
  have hval := congrArg ZMod.val huv
  rw [blockPosition_val, blockPosition_val] at hval
  have hkval : k.val = l.val := by
    have hmod := congrArg (fun n : Nat => n % ell) hval
    simpa [Nat.add_mod, Nat.mul_mod,
      Nat.mod_eq_of_lt k.isLt, Nat.mod_eq_of_lt l.isLt] using hmod
  have hmul : u.val * ell = v.val * ell := by
    rw [hkval] at hval
    exact Nat.add_right_cancel hval
  have huval : u.val = v.val :=
    Nat.eq_of_mul_eq_mul_right (NeZero.pos ell) hmul
  exact Prod.ext
    (ZMod.val_injective ell huval)
    (Fin.ext hkval)
noncomputable def blockEquiv
    (ell : Nat) [NeZero ell] :
    (ZMod ell × Fin ell) ≃ ZMod (ell * ell) :=
  Equiv.ofBijective (blockPosition ell)
    ((Fintype.bijective_iff_injective_and_card
      (blockPosition ell)).2
      ⟨blockPosition_injective ell, by simp [ZMod.card]⟩)
def step
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) : ZMod ell :=
  ((RandomTwist.typeTwist sample τ).val + 1 : Nat)
def typeTranslation
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) : Equiv.Perm (ZMod ell) :=
  Equiv.addRight (step sample τ)
def outNeighbor
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) (u : ZMod ell) : ZMod ell :=
  typeTranslation sample τ u
def inNeighbor
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) (u : ZMod ell) : ZMod ell :=
  (typeTranslation sample τ).symm u
noncomputable def checkSyndrome
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) (a : Fin (3 * r)) : ZMod 2 :=
  ∑ b : Fin (4 * r),
    RandomBase.boundary baseSample a b *
      if RandomTwist.isTail twistSample a b then
        w (u, b)
      else
        w
          (outNeighbor twistSample
            (RandomTwist.checkType typeCount a) u, b)
noncomputable def violationSet
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    Finset (ZMod ell × Fin (3 * r)) := by
  classical
  exact Finset.univ.filter fun ua =>
    checkSyndrome baseSample twistSample w ua.1 ua.2 ≠ 0
noncomputable def violationCount
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) : Nat :=
  (violationSet baseSample twistSample w).card
noncomputable def checkColumn
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (a : Fin (3 * r)) :
    Word (ZMod 2) (ZMod ell) :=
  fun u => checkSyndrome baseSample twistSample w u a
def layerWord
    {r ell : Nat}
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) : Word (ZMod 2) (Fin (4 * r)) :=
  fun b => w (u, b)
def variableWord
    {r ell : Nat}
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (b : Fin (4 * r)) : Word (ZMod 2) (ZMod ell) :=
  fun u => w (u, b)
def HasHHO20LocalTestability
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) : Prop :=
  ∀ w : Word (ZMod 2) (ZMod ell × Fin (4 * r)),
    5000 * Delta * HammingWeight w ≤ ell * (4 * r) →
      HammingWeight w ≤
        250 * violationCount baseSample twistSample w
end QEC.Coding.FiberBundle.TwistGraph


