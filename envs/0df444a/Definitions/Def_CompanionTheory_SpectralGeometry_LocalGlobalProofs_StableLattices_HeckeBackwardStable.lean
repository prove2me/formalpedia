-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeBackwardStable
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeBackwardStable
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T12:39:52.874555+00:00
-- url     : https://prove2.me/theorems/269dea46-81fe-4268-8c9c-bafd9133dd1d
-- title:
--   Hecke Backward Stable
-- statement:
--   Definitions and structural lemmas for Hecke Backward Stable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeBackwardStable.lean

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace GlobalTheory.CompanionTheory.RgHeckeBack
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (tensVd eeVd)
open CompanionTheory.RgExh CompanionTheory.RgExh.Hk
variable {n : ℕ}
end GlobalTheory.CompanionTheory.RgHeckeBack


