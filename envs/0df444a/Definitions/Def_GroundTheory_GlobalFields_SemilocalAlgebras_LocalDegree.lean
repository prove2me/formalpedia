-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_LocalDegree
-- name    : GroundTheory_GlobalFields_SemilocalAlgebras_LocalDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:11.674799+00:00
-- url     : https://prove2.me/theorems/eb852905-d5af-4499-a173-f6ee54228250
-- title:
--   Local Degree
-- statement:
--   Definitions and structural lemmas for Local Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
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
open IsDedekindDomain NumberField WithZero
noncomputable section
namespace SemiLocal
section Integers
variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
end Integers
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]
variable {ι : Type*} [Fintype ι]
end SemiLocal
end
end GroundTheory.Global


