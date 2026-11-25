-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighExistenceHolds
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighExistenceHolds
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T11:24:05.368798+00:00
-- url     : https://prove2.me/theorems/1862a35e-013c-5b5b-b674-0196dcf3b803
-- title:
--   High Existence Holds
-- statement:
--   Definitions and structural lemmas for High Existence Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/HighExistenceHolds.lean

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
open MvPolynomial
section Grade
variable {σ : Type*}
def TGood (w : σ → ℕ) (c d : ℕ) (F : Polynomial (MvPolynomial σ ℂ)) : Prop :=
  ∀ j m, coeff m (F.coeff j) ≠ 0 → Finsupp.weight w m + j * c = d
end Grade
end Formalism.L2.SG.Pf.ColDictValCPf


