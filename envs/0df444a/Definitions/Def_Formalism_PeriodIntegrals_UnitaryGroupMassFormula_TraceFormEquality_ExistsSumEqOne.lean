-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceFormEquality_ExistsSumEqOne
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceFormEquality_ExistsSumEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:18.90256+00:00
-- url     : https://prove2.me/theorems/3dc9fc01-50c2-4b1f-bff8-50af1eb9d6ba
-- title:
--   Exists Sum Eq One
-- statement:
--   Definitions and structural lemmas for Exists Sum Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceFormEquality/ExistsSumEqOne.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.Dv.HermitianFormEquivalence
open PI.Dv
section Ideal
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
def phi (T : GoodSet K G) (s : T.S) : Module.End K (T.W s) →ₗ[K] MonoidAlgebra K G :=
  ∑ y : G, ((((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K)) •
    (LinearMap.trace K (T.W s) ∘ₗ LinearMap.mulRight K (T.tau s y⁻¹))).smulRight
      (MonoidAlgebra.of K G y)
end Ideal
end PI.Dv.HermitianFormEquivalence


