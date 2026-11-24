-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChart
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:34:47.570724+00:00
-- url     : https://prove2.me/theorems/8e6fbf2a-af35-40b6-9d8a-97a2eff43666
-- title:
--   An Chart
-- statement:
--   Definitions and structural lemmas for An Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AnChart.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChartA
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
def zeroSet (K : Ideal (MvPolynomial (Fin n) ℂ)) : Set (Fin n → ℂ) :=
  {y | ∀ h ∈ K, eval y h = 0}
def evalFam {e : ℕ} (r : Fin e → MvPolynomial (Fin n) ℂ) (y : Fin n → ℂ) : Fin e → ℂ :=
  fun i => eval y (r i)
end
end ReciprocityTheory.AnForm.R


