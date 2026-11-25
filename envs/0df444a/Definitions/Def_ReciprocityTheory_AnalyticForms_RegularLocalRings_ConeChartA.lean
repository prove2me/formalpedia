-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T13:41:18.390599+00:00
-- url     : https://prove2.me/theorems/5609a9c7-7ff5-59e8-a08b-137ca605e106
-- title:
--   Cone Chart A
-- statement:
--   Definitions and structural lemmas for Cone Chart A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChartA.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open MvPolynomial Algebra
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
open Classical in

noncomputable def blockWt (k : K) (q : Σ k, ι k) : ℕ := if q.1 = k then 1 else 0
end ReciprocityTheory.AnForm.R


