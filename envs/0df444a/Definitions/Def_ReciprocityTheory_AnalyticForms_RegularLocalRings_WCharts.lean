-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WCharts
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_WCharts
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T14:30:37.89355+00:00
-- url     : https://prove2.me/theorems/c9a1eb52-b3c7-56bb-9713-cb9c2640de10
-- title:
--   WCharts
-- statement:
--   Definitions and structural lemmas for WCharts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WCharts.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
end
end ReciprocityTheory.AnForm.R


