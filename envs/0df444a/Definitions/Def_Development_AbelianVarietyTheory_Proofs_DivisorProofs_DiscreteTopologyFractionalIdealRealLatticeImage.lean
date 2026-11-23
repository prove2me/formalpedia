-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiscreteTopologyFractionalIdealRealLatticeImage
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiscreteTopologyFractionalIdealRealLatticeImage
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:53.389708+00:00
-- url     : https://prove2.me/theorems/9ae023b5-8791-4a9a-964b-03cdb8cebce7
-- title:
--   Discrete Topology Fractional Ideal Real Lattice Image
-- statement:
--   Definitions and structural lemmas for Discrete Topology Fractional Ideal Real Lattice Image, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DiscreteTopologyFractionalIdealRealLatticeImage.lean

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
namespace GlobalTheory.LipschitzTR
noncomputable def toMixedTR (F : Type) [Field F] [NumberField F] (x : RSp F) :
    mixedEmbedding.mixedSpace F :=
  (fun w => x (InfinitePlace.embedding_of_isReal w.prop), fun _ => 0)
end GlobalTheory.LipschitzTR


