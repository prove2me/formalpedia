-- Prove2me | Definitions.Def_QEC_Import_Compact_0ca6971f828e2f2d
-- name    : QEC_Import_Compact_0ca6971f828e2f2d
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:50:26.215303+00:00
-- url     : https://prove2.me/theorems/70903265-ca85-4543-9072-653d26bcdbab
-- title:
--   Exact source statement: BPTCommuting Projector Model: joint BCSector Compression second Cut Code Lift eq first Cut Code Lift
-- statement:
--   The exact universally quantified proposition of the linked Lean-QECert source lemma.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/Transport.lean#L155-L185

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Regrouping
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_Transport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 4000000
noncomputable def QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorCompression_secondCutCodeLift_eq_firstCutCodeLift_QECertStatement : Prop :=
∀ {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa] (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)),
let A := M.fourFactorA region
    let D := M.fourFactorD region
    let V := tensorAssociatorUnitary (Semantics.CompositeSystem A pB) pC D
    let Jleft := jointBCSectorEmbeddingLeft (A := A) pB pC
    let Jright := jointBCSectorEmbeddingRight (A := A) pB pC
    (LinearMap.adjoint Jright).comp ((M.secondCutCodeLift region).comp Jright) =
      V.conjOperator ((LinearMap.adjoint Jleft).comp ((M.firstCutCodeLift region).comp Jleft))


