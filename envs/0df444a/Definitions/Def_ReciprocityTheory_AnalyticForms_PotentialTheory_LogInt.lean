-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LogInt
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_LogInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:12.754223+00:00
-- url     : https://prove2.me/theorems/573844d4-a2fa-412e-b8ce-a8927b18274f
-- title:
--   Log Int
-- statement:
--   Definitions and structural lemmas for Log Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/LogInt.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
def LogNormSecLocalStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) (x : X) (y : X), IsSection A L s → y ∈ L.U x → s x y ≠ 0 →
      logNormSec L s y = Real.log ‖s x y‖ - L.φ x y
end
end ReciprocityTheory.AnForm.M


