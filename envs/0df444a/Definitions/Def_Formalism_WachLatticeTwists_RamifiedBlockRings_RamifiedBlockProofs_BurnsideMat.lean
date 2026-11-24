-- Prove2me | Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_BurnsideMat
-- name    : Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_BurnsideMat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:10:20.956331+00:00
-- url     : https://prove2.me/theorems/ad61c1a6-0400-47a2-836a-e51ce8d9344e
-- title:
--   Burnside Mat
-- statement:
--   Definitions and structural lemmas for Burnside Mat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/BurnsideMat.lean

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_CharpolyRevMap
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IdemNormalForm
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AbsolutelyIrreducibleSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
end Formalism.RepresentationBoundsCohomology.ringDataObjects


