-- Prove2me | Definitions.Def_QEC_Import_Typed_462f37e09c90bb92
-- name    : QEC_Import_Typed_462f37e09c90bb92
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:43:58.845171+00:00
-- url     : https://prove2.me/theorems/f2869167-564c-4207-8eb8-d8dd5e007588
-- title:
--   Exact source statement: BPTCommuting Projector Model: second Cut Pleft range finrank le one of region recoverable
-- statement:
--   The exact universally quantified proposition from Lean-QECert.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/LeftRankOne.lean#L30-L67

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftPhysical
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_RankOne
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOne
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 1600000

noncomputable def QEC.Bounds.BPTCommutingProjectorModel.secondCut_Pleft_range_finrank_le_one_of_region_recoverable_QECertTypedStatement : Prop :=
∀ {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa] (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hM : M.RegionErasureRecoverable region)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)),
let A := M.fourFactorA region
    let H := component.1.restrictScalars Complex
    let W0 := W.restrictScalars Complex
    let N := isotypicLiftedMultiplicity.{0} n
    let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
    ∀ (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W0 N))
      (Pleft : Semantics.Operator (Semantics.CompositeSystem A W0))
      (Qright : Semantics.Operator (Semantics.CompositeSystem N CD)),
      M.secondCutCodeLift region * M.secondCutSectorLift region component =
          M.secondCutCodeLift region →
      (unitaryLTensor A U).conjOperator
          (overlapProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) component) =
          rightTensorExtensionAfterLeft A W0 N Pleft →
      (unitaryRTensor U CD).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region) component) =
          leftTensorExtensionBeforeRight W0 N CD Qright →
      Module.finrank Complex (LinearMap.range Pleft) ≤ 1


