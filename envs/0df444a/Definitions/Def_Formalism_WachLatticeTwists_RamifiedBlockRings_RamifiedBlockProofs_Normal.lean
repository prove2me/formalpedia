-- Prove2me | Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_Normal
-- name    : Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_Normal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:28.439932+00:00
-- url     : https://prove2.me/theorems/50812718-3d79-49c3-af44-f5975aff6e0c
-- title:
--   Normal
-- statement:
--   Definitions and structural lemmas for Normal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/Normal.lean

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_CharpolyRevMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
section Normal
variable {O : Type*} [CommRing O] {r : Type} [Fintype r] [DecidableEq r]
end Normal
end Formalism.RepresentationBoundsCohomology.ringDataObjects


