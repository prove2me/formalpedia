-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
-- name    : GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:11:14.073294+00:00
-- url     : https://prove2.me/theorems/0f099bfd-2a8b-480b-81a4-758c87c076ba
-- title:
--   Norm Trace
-- statement:
--   Definitions and structural lemmas for Norm Trace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/NormTrace.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
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
open IsDedekindDomain NumberField TensorProduct Module Matrix
noncomputable section
namespace SemiLocal
variable {R : Type*} [Field R] {ι : Type*} [Fintype ι] {S : ι → Type*} [∀ i, CommRing (S i)]
  [∀ i, Algebra R (S i)] [∀ i, Module.Finite R (S i)]
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))
end SemiLocal
end
end GroundTheory.Global


