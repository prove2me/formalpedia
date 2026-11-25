-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasure
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasure
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T03:51:01.466387+00:00
-- url     : https://prove2.me/theorems/333d8b28-d774-438e-8a91-1ff10565e450
-- title:
--   Ma Measure
-- statement:
--   Definitions and structural lemmas for Ma Measure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/MaMeasure.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
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
def LocDensNonnegStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X),
    (∀ i, IsPotential A (Φ i)) → (∀ i, IsPsh A (Φ i)) →
      ∀ j, ∀ y ∈ (A.chart j).target, 0 ≤ locDens A Φ j y
end
end ReciprocityTheory.AnForm.M


