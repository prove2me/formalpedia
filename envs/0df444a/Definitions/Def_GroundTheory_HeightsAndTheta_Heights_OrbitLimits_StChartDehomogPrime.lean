-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartDehomogPrime
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartDehomogPrime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:28.243863+00:00
-- url     : https://prove2.me/theorems/aae59a5a-fa63-4092-8654-a7b1e3599292
-- title:
--   St Chart Dehomog Prime
-- statement:
--   Definitions and structural lemmas for St Chart Dehomog Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StChartDehomogPrime.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConePolar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
def ChartDehomogPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (W : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F),
    IsProjPrime W → linForm t ∉ W → (W ⊔ Ideal.span {linForm t - 1}).IsPrime
end GroundTheory.Heights₂.Heights


