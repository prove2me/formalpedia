-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_IsUnitDetOfUnitary
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_IsUnitDetOfUnitary
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T11:30:19.767246+00:00
-- url     : https://prove2.me/theorems/96bb6184-799a-526c-8ad3-c1806993e3f3
-- title:
--   Is Unit Det Of Unitary
-- statement:
--   Definitions and structural lemmas for Is Unit Det Of Unitary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/IsUnitDetOfUnitary.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.SG.Pf.ColDictValCPf
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.L2.SG.Pf.ColDictPf Matrix MvPolynomial
open scoped ComplexOrder
section Transfer
variable {ι : Type} [Fintype ι] {n : ℕ}
def detBlocks : MvPolynomial (ι × Fin n × Fin n) ℂ :=
  ∏ τ, (Matrix.of fun a b : Fin n => (X (τ, a, b) : MvPolynomial (ι × Fin n × Fin n) ℂ)).det
end Transfer
end Formalism.L2.SG.Pf.ColDictValCPf


