-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_CompressionExteriorWitness
-- name    : QEC_Bounds_BPTSeparatedUnion_Transport_CompressionExteriorWitness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:00:55.957582+00:00
-- url     : https://prove2.me/theorems/ece62a61-5af3-49a8-956f-b3ad1dc5a3e4
-- title:
--   Compression Exterior Witness
-- statement:
--   Definitions and structural lemmas for Compression Exterior Witness, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/CompressionExteriorWitness.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_ExteriorAction
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionFactorization_conj_exteriorLocal

set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
noncomputable def exteriorCompressionWitness
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem) :
    Semantics.Operator (M.fourFactorD region) :=
  Classical.choose (M.regionFactorization_conj_exteriorLocal region P)
noncomputable def exteriorCompressionComplementAction
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem) :
    Semantics.Operator (M.regionSubsystem region).complementSystem :=
  let S := M.regionSubsystem region
  let T := M.regionSubsystem (region ∪ M.externalBoundary region)
  let splitCD := S.complementFactorization T (by
    intro site hsite
    exact Finset.mem_union_left _ hsite)
  splitCD.symm.conjOperator
    (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region))
      (M.exteriorCompressionWitness region P))
end BPTCommutingProjectorModel
end Bounds
end QEC


