-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_InjectiveOfLinearIndependent
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_InjectiveOfLinearIndependent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:27:53.102727+00:00
-- url     : https://prove2.me/theorems/d81ab280-0f0d-46a1-9091-0b787dc4e2e4
-- title:
--   Injective Of Linear Independent
-- statement:
--   Definitions and structural lemmas for Injective Of Linear Independent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/InjectiveOfLinearIndependent.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_TrBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ExistsEqEllMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField TensorProduct ValuativeRel
namespace PI.ProdFormulaE.Tr
variable {F : Type} [Field F] [NumberField F] {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type}
end PI.ProdFormulaE.Tr


