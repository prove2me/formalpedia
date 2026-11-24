-- Prove2me | Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_DensityPointOfCornerSimple
-- name    : Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_DensityPointOfCornerSimple
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:46:45.423246+00:00
-- url     : https://prove2.me/theorems/dfb4c50a-6a67-41e3-9383-eb1d353cc5bd
-- title:
--   Density Point Of Corner Simple
-- statement:
--   Definitions and structural lemmas for Density Point Of Corner Simple, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/DensityPointOfCornerSimple.lean

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_FinrankRangeEq
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdemFactor
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdempotentImageSurjective
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
section Pts
variable {O : Type} [CommRing O] [IsDomain O] {X : Type} (T : Subalgebra O (X → O)) {d : Type} [Fintype d]
  [DecidableEq d] {G : Type} [Group G] (r : G →* (X → Matrix d d O))
end Pts
end Formalism.RepresentationBoundsCohomology.ringDataObjects


