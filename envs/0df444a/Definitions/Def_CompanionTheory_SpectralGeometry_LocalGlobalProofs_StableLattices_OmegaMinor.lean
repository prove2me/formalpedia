-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_OmegaMinor
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_OmegaMinor
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T13:36:42.507158+00:00
-- url     : https://prove2.me/theorems/2defc150-d297-46ed-97de-e4d8dc81c038
-- title:
--   Omega Minor
-- statement:
--   Definitions and structural lemmas for Omega Minor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/OmegaMinor.lean

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEqualityStatement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_capelliExpand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
namespace GlobalTheory.CompanionTheory.HeckeCapelli
open CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (cminor capelliC capEntry capelliExpand)
end GlobalTheory.CompanionTheory.HeckeCapelli


