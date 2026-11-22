-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_IntRootProp
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_IntRootProp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:47.366638+00:00
-- url     : https://prove2.me/theorems/62202426-971d-4d36-9f2a-74c194692d99
-- title:
--   Int Root Prop
-- statement:
--   Definitions and structural lemmas for Int Root Prop, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitKronecker/IntRootProp.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.UnitKronW
open Polynomial NumberField
def IntRootProp : Prop :=
  ∀ (E L : Type) [Field E] [Field L] [Algebra E L] (p : E[X]), p.Monic → (∀ i, IsIntegral ℤ (p.coeff i)) →
    ∀ x : L, (p.map (algebraMap E L)).IsRoot x → IsIntegral ℤ x
end PI.UnitKronW
namespace PI.UnitKronW
open Polynomial
end PI.UnitKronW


