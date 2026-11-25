-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
-- name    : GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:27:46.021729+00:00
-- url     : https://prove2.me/theorems/253fe17f-3cbd-4be4-8fa2-cf9a67e71931
-- title:
--   Trace Lattice Poisson
-- statement:
--   Definitions and structural lemmas for Trace Lattice Poisson, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceLatticePoisson.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticeEuclidean
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical RealInnerProductSpace FourierTransform SchwartzMap nonZeroDivisors
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
end
end GroundTheory.Global


