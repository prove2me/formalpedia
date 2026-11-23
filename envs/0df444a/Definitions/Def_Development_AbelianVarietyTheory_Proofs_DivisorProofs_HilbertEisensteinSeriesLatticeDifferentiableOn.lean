-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinSeriesLatticeDifferentiableOn
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinSeriesLatticeDifferentiableOn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:01:26.062594+00:00
-- url     : https://prove2.me/theorems/b656bc71-72dd-4d1e-a012-454ca1e49f8b
-- title:
--   Hilbert Eisenstein Series Lattice Differentiable On
-- statement:
--   Definitions and structural lemmas for Hilbert Eisenstein Series Lattice Differentiable On, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinSeriesLatticeDifferentiableOn.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_NormFderivLeOfClosedBallSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open Metric Complex
namespace GlobalTheory
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
end GlobalTheory


