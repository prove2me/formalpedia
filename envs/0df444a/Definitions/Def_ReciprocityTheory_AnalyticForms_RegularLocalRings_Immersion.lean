-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Immersion
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_Immersion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:39.05137+00:00
-- url     : https://prove2.me/theorems/c9ab56f0-42ee-45a3-b1c6-c1c1115bb49d
-- title:
--   Immersion
-- statement:
--   Definitions and structural lemmas for Immersion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/Immersion.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsAtlas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open MvPolynomial ReciprocityTheory.AnForm.M Topology Filter
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
end ReciprocityTheory.AnForm.R


