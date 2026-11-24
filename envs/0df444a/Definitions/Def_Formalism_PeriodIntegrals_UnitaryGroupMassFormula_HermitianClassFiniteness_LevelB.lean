-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_LevelB
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_LevelB
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T15:53:24.216257+00:00
-- url     : https://prove2.me/theorems/740f0206-0a40-4bae-b860-2760517829c9
-- title:
--   Level B
-- statement:
--   Definitions and structural lemmas for Level B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/LevelB.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_LevelA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Lemmata_IntegerMulIntegral_IntMulIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix IsDedekindDomain Formalism.UG Formalism.UG.P PI.InHHClassFin
open scoped TensorProduct
namespace PI.UnitaryGroupMassFormula.InHHClassFin
section Adelic
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
end Adelic
end PI.UnitaryGroupMassFormula.InHHClassFin


