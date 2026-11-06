-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
-- name    : QEC_Coding_FiberBundle_CohomologyDistance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:50:45.550947+00:00
-- url     : https://prove2.me/theorems/f514e682-4cea-426e-8ec3-8ec01bfff350
-- title:
--   Cohomology Distance
-- statement:
--   Definitions and structural lemmas for Cohomology Distance, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_groupedDistribution_apply
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
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.columnDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.groupedDistribution_apply
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
namespace QEC.Coding.FiberBundle
universe u
def horizontalComponent
    {baseZero baseOne fiberZero fiberOne : Type u}
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    Word (ZMod 2) (baseOne × fiberZero) :=
  fun bi => x (Sum.inl bi)
@[simp]
theorem horizontalComponent_add
    {baseZero baseOne fiberZero fiberOne : Type u}
    (x y : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    horizontalComponent (x + y) =
      horizontalComponent x + horizontalComponent y := by
  rfl
def verticalComponent
    {baseZero baseOne fiberZero fiberOne : Type u}
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    Word (ZMod 2) (baseZero × fiberOne) :=
  fun aj => x (Sum.inr aj)
def horizontalBaseLift
    {baseZero baseOne fiberZero fiberOne : Type u}
    (x : Word (ZMod 2) baseOne) :
    Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)
  | Sum.inl (b, _i) => x b
  | Sum.inr _ => 0
@[simp]
theorem horizontalBaseLift_add
    {baseZero baseOne fiberZero fiberOne : Type u}
    (x y : Word (ZMod 2) baseOne) :
    horizontalBaseLift
        (baseZero := baseZero) (fiberZero := fiberZero)
        (fiberOne := fiberOne) (x + y) =
      horizontalBaseLift
          (baseZero := baseZero) (fiberZero := fiberZero)
          (fiberOne := fiberOne) x +
        horizontalBaseLift
          (baseZero := baseZero) (fiberZero := fiberZero)
          (fiberOne := fiberOne) y := by
  funext q
  rcases q with bi | aj
  · rfl
  · rfl
@[simp]
theorem verticalComponent_horizontalBaseLift_add
    {baseZero baseOne fiberZero fiberOne : Type u}
    (x : Word (ZMod 2) baseOne)
    (y : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    verticalComponent
        (horizontalBaseLift
          (baseZero := baseZero) (fiberZero := fiberZero)
          (fiberOne := fiberOne) x + y) =
      verticalComponent y := by
  funext aj
  simp [verticalComponent, horizontalBaseLift]
def horizontalFiber
    {baseZero baseOne fiberZero fiberOne : Type u}
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne))
    (b : baseOne) : Word (ZMod 2) fiberZero :=
  fun i => x (Sum.inl (b, i))
@[simp]
theorem horizontalFiber_horizontalBaseLift
    {baseZero baseOne fiberZero fiberOne : Type u}
    (x : Word (ZMod 2) baseOne) (b : baseOne) :
    horizontalFiber
      (horizontalBaseLift
        (baseZero := baseZero) (fiberZero := fiberZero)
        (fiberOne := fiberOne) x) b =
      fun _i => x b := by
  rfl
def verticalFiber
    {baseZero baseOne fiberZero fiberOne : Type u}
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne))
    (a : baseZero) : Word (ZMod 2) fiberOne :=
  fun j => x (Sum.inr (a, j))
def c0Fiber
    {baseZero fiberZero : Type u}
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (a : baseZero) : Word (ZMod 2) fiberZero :=
  fun i => u (a, i)
noncomputable def c0Shadow
    {baseZero fiberZero : Type u}
    [Fintype baseZero] [Fintype fiberZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero)) :
    Finset baseZero :=
  Finset.univ.filter fun a => c0Fiber u a ≠ 0
noncomputable def horizontalShadow
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseOne] [Fintype fiberZero]
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    Finset baseOne :=
  Finset.univ.filter fun b => horizontalFiber x b ≠ 0
noncomputable def verticalShadow
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [Fintype fiberOne]
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    Finset baseZero :=
  Finset.univ.filter fun a => verticalFiber x a ≠ 0
def cycleFiberCoboundary
    (n : Nat) [NeZero n]
    (f : Word (ZMod 2) (ZMod n)) :
    Word (ZMod 2) (ZMod n) :=
  fun j => ∑ i : ZMod n, f i * cycleBoundary n i j
def reindexWord
    {ι κ : Type u} (e : ι ≃ κ) (x : Word (ZMod 2) ι) :
    Word (ZMod 2) κ :=
  fun k => x (e.symm k)
def binaryComplement
    {ι : Type u} (x : Word (ZMod 2) ι) : Word (ZMod 2) ι :=
  fun i => 1 + x i
def normalizeBinaryWord
    {ι : Type u} [Fintype ι] (x : Word (ZMod 2) ι) :
    Word (ZMod 2) ι :=
  if 2 * HammingWeight x ≤ Fintype.card ι then x else binaryComplement x
def normalizeC0Fibers
    {baseZero fiberZero : Type u}
    [Fintype fiberZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero)) :
    Word (ZMod 2) (C0Index baseZero fiberZero) :=
  fun ai => normalizeBinaryWord (fun i => u (ai.1, i)) ai.2
def normalizationToggle
    {baseZero fiberZero : Type u}
    [Fintype fiberZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (a : baseZero) : ZMod 2 :=
  if 2 * HammingWeight (fun i => u (a, i)) ≤ Fintype.card fiberZero
  then 0
  else 1
def normalizationToggleWord
    {baseZero fiberZero : Type u}
    [Fintype fiberZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero)) :
    Word (ZMod 2) (C0Index baseZero fiberZero) :=
  fun ai => normalizationToggle u ai.1
def baseCoboundary
    {r : Nat}
    (baseSample : RandomBase.Sample r)
    (t : Word (ZMod 2) (Fin (3 * r))) :
    Word (ZMod 2) (Fin (4 * r)) :=
  fun b =>
    ∑ a : Fin (3 * r), t a * RandomBase.boundary baseSample a b
def IsNontrivialBaseCohomology
    {r : Nat}
    (baseSample : RandomBase.Sample r)
    (x : Word (ZMod 2) (Fin (4 * r))) : Prop :=
  ∀ t : Word (ZMod 2) (Fin (3 * r)), x ≠ baseCoboundary baseSample t
def normalizationBaseShift
    {r ell : Nat}
    [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell)))) :
    Word (ZMod 2) (Fin (4 * r)) :=
  baseCoboundary baseSample (normalizationToggle u)
def eraseC0FiberCorrection
    {baseZero fiberZero : Type u}
    [DecidableEq baseZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (a : baseZero) :
    Word (ZMod 2) (C0Index baseZero fiberZero) :=
  fun ai => if ai.1 = a then -u ai else 0
def eraseC0Fiber
    {baseZero fiberZero : Type u}
    [DecidableEq baseZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (a : baseZero) :
    Word (ZMod 2) (C0Index baseZero fiberZero) :=
  u + eraseC0FiberCorrection u a
@[simp]
theorem c0Fiber_eraseC0Fiber_same
    {baseZero fiberZero : Type u}
    [DecidableEq baseZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (a : baseZero) :
    c0Fiber (eraseC0Fiber u a) a = 0 := by
  funext i
  simp only [c0Fiber, eraseC0Fiber, Pi.add_apply, eraseC0FiberCorrection,
    Pi.zero_apply]
  exact add_neg_cancel _
theorem c0Fiber_eraseC0Fiber_of_ne
    {baseZero fiberZero : Type u}
    [DecidableEq baseZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    {a a' : baseZero} (ha : a' ≠ a) :
    c0Fiber (eraseC0Fiber u a) a' = c0Fiber u a' := by
  funext i
  simp [c0Fiber, eraseC0Fiber, eraseC0FiberCorrection, ha]
def C0FibersNormalized
    {baseZero fiberZero : Type u}
    [Fintype fiberZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero)) : Prop :=
  ∀ a, 2 * HammingWeight (c0Fiber u a) ≤ Fintype.card fiberZero
theorem C0FibersNormalized.eraseC0Fiber
    {baseZero fiberZero : Type u}
    [DecidableEq baseZero] [Fintype fiberZero]
    {u : Word (ZMod 2) (C0Index baseZero fiberZero)}
    (hu : C0FibersNormalized u) (a : baseZero) :
    C0FibersNormalized (eraseC0Fiber u a) := by
  intro a'
  by_cases ha : a' = a
  · subst a'
    rw [c0Fiber_eraseC0Fiber_same, HammingWeight_zero]
    exact Nat.zero_le _
  · rw [c0Fiber_eraseC0Fiber_of_ne u ha]
    exact hu a'
noncomputable def bundleCoboundary
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (u : Word (ZMod 2) (C0Index baseZero fiberZero)) :
    Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne) :=
  wordLinearMapTranspose (boundary1 D) u
def IsHorizontalWeightMinimal
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell)))) : Prop :=
  ∀ v : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))),
    HammingWeight
        (horizontalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u)) ≤
      HammingWeight
        (horizontalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) v))
def IsWeightMinimal
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell)))) : Prop :=
  ∀ v : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))),
    HammingWeight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) u) ≤
      HammingWeight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) v)
end QEC.Coding.FiberBundle


