-- Prove2me | Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_Length
-- name    : Formalism_GrowthSums_FactorialBaseGrowth_Length
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:27:30.10325+00:00
-- url     : https://prove2.me/theorems/b13583fc-7486-42c0-97b0-91524588ed43
-- title:
--   Length
-- statement:
--   Definitions and structural lemmas for Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/Length.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace Formalism.GrowthSums
namespace ModuleLengthMonotonicity
variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
abbrev len (W U : Submodule R X) : ℕ∞ := Module.length R (W ⧸ U.comap W.subtype)
variable [IsDomain R] [IsDiscreteValuationRing R]
end ModuleLengthMonotonicity
end Formalism.GrowthSums


