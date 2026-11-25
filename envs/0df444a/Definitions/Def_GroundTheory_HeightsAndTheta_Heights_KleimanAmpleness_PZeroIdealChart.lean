-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PZeroIdealChart
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PZeroIdealChart
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:24:18.143678+00:00
-- url     : https://prove2.me/theorems/6fa05544-3342-530f-b4e5-97317a0e5b2f
-- title:
--   PZero Ideal Chart
-- statement:
--   Definitions and structural lemmas for PZero Ideal Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PZeroIdealChart.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsZeroIdealChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
section ZeroIdealChartAux
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
def chartUnion (I K : Chart x) : Chart x :=
  ⟨I.1 ∪ K.1, I.2.1.mono Finset.subset_union_left, Finset.union_subset I.2.2 K.2.2⟩
end ZeroIdealChartAux
end
end GroundTheory.Heights₂.Heights.Kleiman


