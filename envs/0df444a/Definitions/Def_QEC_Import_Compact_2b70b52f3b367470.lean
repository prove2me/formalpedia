-- Prove2me | Definitions.Def_QEC_Import_Compact_2b70b52f3b367470
-- name    : QEC_Import_Compact_2b70b52f3b367470
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:56:16.473313+00:00
-- url     : https://prove2.me/theorems/b89c3d1f-6d8d-4ae2-b251-6eacb2a67954
-- title:
--   Exact source statement: BPTCommuting Projector Model: isotypic Tensor Left Action adjoint
-- statement:
--   The exact universally quantified proposition of the linked Lean-QECert source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3970-L3977

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
set_option autoImplicit false
universe checked_u0
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.isotypicTensorLeftAction_adjoint_QECertStatement : Prop :=
∀ {B : Type checked_u0} [inst : NormedAddCommGroup B] [inst_1 : InnerProductSpace ℂ B]
  [inst_2 : QEC.Semantics.FiniteQuantumSystem B] (S : StarSubalgebra ℂ (QEC.Semantics.Operator B))
  (W : Submodule (↥S) B) (n : ℕ) (operator : ↥S),
  LinearMap.adjoint (QEC.Bounds.BPTCommutingProjectorModel.isotypicTensorLeftAction S W n operator) =
    QEC.Bounds.BPTCommutingProjectorModel.isotypicTensorLeftAction S W n (Star.star operator)


