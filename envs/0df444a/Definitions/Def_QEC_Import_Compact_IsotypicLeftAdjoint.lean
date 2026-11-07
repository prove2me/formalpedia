-- Prove2me | Definitions.Def_QEC_Import_Compact_IsotypicLeftAdjoint
-- name    : QEC_Import_Compact_IsotypicLeftAdjoint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:59:24.648484+00:00
-- url     : https://prove2.me/theorems/1d4e6860-5091-424f-9ba3-5d81dd6ee813
-- title:
--   Isotypic left action adjoint statement
-- statement:
--   The exact universally quantified statement of the source isotypic left action adjoint lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3316-L3337

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
universe checked_u
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.isotypicLeftAction_adjoint_QECertStatement : Prop :=
∀ {B : Type checked_u} [inst : NormedAddCommGroup B] [inst_1 : InnerProductSpace ℂ B]
  [inst_2 : QEC.Semantics.FiniteQuantumSystem B] (S : StarSubalgebra ℂ (QEC.Semantics.Operator B))
  (component : ↑(isotypicComponents (↥S) B)) (operator : ↥S),
  LinearMap.adjoint (QEC.Bounds.BPTCommutingProjectorModel.isotypicLeftAction S component operator) =
    QEC.Bounds.BPTCommutingProjectorModel.isotypicLeftAction S component (Star.star operator)


