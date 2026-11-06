-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_SelectedB
-- name    : QEC_Bounds_BPTDisentangling_ScalarCompression_SelectedB
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:51:51.196503+00:00
-- url     : https://prove2.me/theorems/f98fdd20-4b67-462a-a982-45087a87e052
-- title:
--   Selected B
-- statement:
--   Definitions and structural lemmas for Selected B, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/SelectedB.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneBlock
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
def secondCutSelectedBEmbedding
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region)) :
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) pB)
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) →ₗ[Complex]
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) :=
  tensorTripleSubtypeEmbedding (A := M.fourFactorA region)
    (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) pB
noncomputable def secondCutSelectedBCompression
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region)) :
    Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) pB)
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) :=
  (LinearMap.adjoint (M.secondCutSelectedBEmbedding region pB)).comp
    ((M.secondCutCodeLift region).comp (M.secondCutSelectedBEmbedding region pB))
end BPTCommutingProjectorModel
end Bounds
end QEC


