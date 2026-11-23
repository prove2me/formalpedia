-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_ExistsStarMulSelf
-- name    : Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_ExistsStarMulSelf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:55:02.330214+00:00
-- url     : https://prove2.me/theorems/980422f5-c80a-4a01-a5b6-2118af50d1b5
-- title:
--   Exists Star Mul Self
-- statement:
--   Definitions and structural lemmas for Exists Star Mul Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/ExistsStarMulSelf.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
namespace Formalism.L2.Geo.Rec.TraceQuadraticBound
variable {n : Type} [Fintype n] [DecidableEq n]
section Dense
variable {K : Type} [Field K]
end Dense
end Formalism.L2.Geo.Rec.TraceQuadraticBound
open NumberField NumberField.InfinitePlace
namespace Formalism.L2.Geo.Rec.TraceSumEmbeddings
variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
end Formalism.L2.Geo.Rec.TraceSumEmbeddings


