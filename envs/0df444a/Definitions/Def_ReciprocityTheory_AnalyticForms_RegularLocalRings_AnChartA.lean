-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChartA
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChartA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:46.650969+00:00
-- url     : https://prove2.me/theorems/219ff995-854c-4e20-b02e-11003a62667a
-- title:
--   An Chart A
-- statement:
--   Definitions and structural lemmas for An Chart A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AnChartA.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_ExistsAnalyticGraphChartMvPolynomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {n : ℕ}
def dualEv (p v : Fin n → ℂ) : MvPolynomial (Fin n) ℂ →ₐ[ℂ] DualNumber ℂ :=
  aeval fun j => (TrivSqZeroExt.inl (p j) + v j • DualNumber.eps : DualNumber ℂ)
end
end ReciprocityTheory.AnForm.R


