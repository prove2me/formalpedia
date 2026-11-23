-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShift
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_PshShift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:39:15.704972+00:00
-- url     : https://prove2.me/theorems/1d927db1-25e3-4567-b331-bbeca1bba174
-- title:
--   Psh Shift
-- statement:
--   Definitions and structural lemmas for Psh Shift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PshShift.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftB
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
open scoped ContDiff
noncomputable section
def LeviCompStatement : Prop :=
  ∀ {e e' : ℕ} (φ : (Fin e' → ℂ) → ℝ) (τ : (Fin e → ℂ) → (Fin e' → ℂ)) (z w : Fin e → ℂ),
    AnalyticAt ℂ τ z → ContDiffAt ℝ 2 φ (τ z) →
      levi (φ ∘ τ) z w = levi φ (τ z) (fderiv ℂ τ z w)
end
end ReciprocityTheory.AnForm.M


