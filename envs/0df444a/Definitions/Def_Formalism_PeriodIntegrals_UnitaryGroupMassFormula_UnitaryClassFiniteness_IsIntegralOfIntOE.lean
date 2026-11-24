-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T13:30:22.453308+00:00
-- url     : https://prove2.me/theorems/baddbedf-164e-4d42-839c-92074305b669
-- title:
--   Is Integral Of Int OE
-- statement:
--   Definitions and structural lemmas for Is Integral Of Int OE, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/IsIntegralOfIntOE.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
namespace PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (F E) in

def Oh : AddSubgroup (Af F ⊗[F] E) :=
  AddSubgroup.closure {r | ∃ a ∈ intAf F, ∃ e : E, IsIntegral ℤ e ∧ r = a ⊗ₜ[F] e}
end PI.UnitaryGroupMassFormula.UJClassFin


