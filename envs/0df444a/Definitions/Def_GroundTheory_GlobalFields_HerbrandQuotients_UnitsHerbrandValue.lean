-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrandValue
-- name    : GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrandValue
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T04:52:00.727706+00:00
-- url     : https://prove2.me/theorems/235e6d14-135e-42c1-8ff1-47a368eb9bce
-- title:
--   Units Herbrand Value
-- statement:
--   Definitions and structural lemmas for Units Herbrand Value, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/UnitsHerbrandValue.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open NumberField NumberField.Units NumberField.InfinitePlace MulAction Module
open scoped TensorProduct
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
def logLatticeProdMap : logLattice L × ℤ →ₗ[ℤ] (InfinitePlace L → ℝ) :=
  (logLattice L).subtype.coprod (LinearMap.toSpanSingleton ℤ (InfinitePlace L → ℝ) 1)
variable [IsGalois K L]
end
end GroundTheory.Global


