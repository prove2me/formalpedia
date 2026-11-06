-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_SequentialEmbeddingCore
-- name    : QEC_Bounds_BPTDisentangling_Joint_Compression_SequentialEmbeddingCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T16:42:34.93125+00:00
-- url     : https://prove2.me/theorems/da841877-3aa5-46c4-be45-53cf13cda849
-- title:
--   Sequential Embedding Core
-- statement:
--   Definitions and structural lemmas for Sequential Embedding Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/SequentialEmbeddingCore.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_ResidualProjection
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_SelectedB
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
def secondCutSelectedCAfterBEmbedding
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) pB)
      (Semantics.CompositeSystem pC (M.fourFactorD region))) →ₗ[Complex]
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) pB)
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) :=
  TensorProduct.map (1 : Semantics.Operator
    (Semantics.CompositeSystem (M.fourFactorA region) pB))
    (TensorProduct.map pC.subtype (1 : Semantics.Operator (M.fourFactorD region)))
def firstCutSelectedCEmbedding
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pC : Submodule Complex (M.fourFactorC region)) :
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)) pC)
      (M.fourFactorD region)) →ₗ[Complex]
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (M.fourFactorC region))
      (M.fourFactorD region)) :=
  tensorTripleSubtypeEmbedding
    (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
    (C := M.fourFactorD region) pC
def firstCutSelectedBAfterCEmbedding
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem (Semantics.CompositeSystem (M.fourFactorA region) pB) pC)
      (M.fourFactorD region)) →ₗ[Complex]
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)) pC)
      (M.fourFactorD region)) :=
  TensorProduct.map
    (TensorProduct.map
      (TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region)) pB.subtype)
      (1 : Semantics.Operator pC))
    (1 : Semantics.Operator (M.fourFactorD region))
noncomputable def firstCutSelectedCCompression
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pC : Submodule Complex (M.fourFactorC region)) :
    Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)) pC)
      (M.fourFactorD region)) :=
  (LinearMap.adjoint (M.firstCutSelectedCEmbedding region pC)).comp
    ((M.firstCutCodeLift region).comp (M.firstCutSelectedCEmbedding region pC))
noncomputable def sequentialSecondCutJointCompression
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) pB)
      (Semantics.CompositeSystem pC (M.fourFactorD region))) :=
  (LinearMap.adjoint (M.secondCutSelectedCAfterBEmbedding region pB pC)).comp
    ((M.secondCutSelectedBCompression region pB).comp
      (M.secondCutSelectedCAfterBEmbedding region pB pC))
noncomputable def sequentialFirstCutJointCompression
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem (Semantics.CompositeSystem (M.fourFactorA region) pB) pC)
      (M.fourFactorD region)) :=
  (LinearMap.adjoint (M.firstCutSelectedBAfterCEmbedding region pB pC)).comp
    ((M.firstCutSelectedCCompression region pC).comp
      (M.firstCutSelectedBAfterCEmbedding region pB pC))
noncomputable def secondCutJointCompression
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) pB)
      (Semantics.CompositeSystem pC (M.fourFactorD region))) :=
  (LinearMap.adjoint
    (jointBCSectorEmbeddingRight (A := M.fourFactorA region)
      (D := M.fourFactorD region) pB pC)).comp
    ((M.secondCutCodeLift region).comp
      (jointBCSectorEmbeddingRight (A := M.fourFactorA region)
        (D := M.fourFactorD region) pB pC))
end BPTCommutingProjectorModel
end Bounds
end QEC


