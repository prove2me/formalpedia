-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Separation
-- name    : QEC_Bounds_BPTSeparatedUnion_Separation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:13:41.672477+00:00
-- url     : https://prove2.me/theorems/3fbd6324-49ff-4a71-b22f-3ab0c000bda6
-- title:
--   Separation
-- statement:
--   Definitions and structural lemmas for Separation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Separation.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
def ActualProjectorSeparated (M : BPTCommutingProjectorModel L kappa)
    (left right : Finset L.Site) : Prop :=
  ∀ check,
    ¬ (((M.support check) ∩ left).Nonempty ∧
      ((M.support check) ∩ right).Nonempty)
end BPTCommutingProjectorModel
end Bounds
end QEC


