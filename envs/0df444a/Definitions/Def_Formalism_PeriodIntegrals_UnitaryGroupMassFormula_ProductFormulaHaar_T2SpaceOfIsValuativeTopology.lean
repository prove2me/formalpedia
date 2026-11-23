-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_T2SpaceOfIsValuativeTopology
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_T2SpaceOfIsValuativeTopology
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:28:19.617502+00:00
-- url     : https://prove2.me/theorems/a96e519a-045e-4411-9c9d-0f35fc2155d0
-- title:
--   T2 Space Of Is Valuative Topology
-- statement:
--   Definitions and structural lemmas for T2 Space Of Is Valuative Topology, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/T2SpaceOfIsValuativeTopology.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_TrBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField TensorProduct ValuativeRel Filter Topology
namespace PI.ProdFormulaE.Tr
variable {F : Type} [Field F] [NumberField F]
variable {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type}
end PI.ProdFormulaE.Tr


