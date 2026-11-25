-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GlobalFunctionsIntegralSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GlobalFunctionsIntegralSt
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T05:55:36.11261+00:00
-- url     : https://prove2.me/theorems/e59af7b5-84ed-41c2-a479-5371cd2d9e54
-- title:
--   Global Functions Integral St
-- statement:
--   Definitions and structural lemmas for Global Functions Integral St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/GlobalFunctionsIntegralSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
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
def GlobalFunctionsIntegral.Statement : Prop :=
  ∀ (k : Type u) [Field k] (K : Type w) [Field K] [Algebra k K] (N : ℕ) (y : Fin (N + 1) → K) (a : K),
    y ≠ 0 → (∀ (i : Fin (N + 1)) (hi : y i ≠ 0), a ∈ chartRing k y (singleChart hi)) → IsIntegral k a
end
end GroundTheory.Heights₂.Heights.Kleiman


