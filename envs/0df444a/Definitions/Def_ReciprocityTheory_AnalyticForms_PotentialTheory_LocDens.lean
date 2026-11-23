-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:37.47453+00:00
-- url     : https://prove2.me/theorems/61829749-363e-448d-922d-68deeb12fd87
-- title:
--   Loc Dens
-- statement:
--   Definitions and structural lemmas for Loc Dens, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/LocDens.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff ComplexOrder Matrix
noncomputable section
def HessCGermStatement : Prop :=
  ∀ {D : ℕ} (φ ψ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ), φ =ᶠ[nhds z] ψ → hessC φ z = hessC ψ z
end
end ReciprocityTheory.AnForm.M


