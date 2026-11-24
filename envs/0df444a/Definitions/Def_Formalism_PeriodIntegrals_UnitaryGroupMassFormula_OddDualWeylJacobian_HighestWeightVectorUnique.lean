-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightVectorUnique
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightVectorUnique
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:54.113792+00:00
-- url     : https://prove2.me/theorems/576d9bba-9a45-43b7-abd4-53873b665aed
-- title:
--   Highest Weight Vector Unique
-- statement:
--   Definitions and structural lemmas for Highest Weight Vector Unique, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightVectorUnique.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Lemmata_GeneralBFactRightAlt_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
namespace PI.OddDualWeyl.Uniq
def P (Rg : Type*) [CommRing Rg] (k : ℕ) : Matrix (Fin k) (Fin k) Rg :=
  Matrix.of fun i j => if i = Fin.rev j then 1 else 0
variable {Rg : Type*} [CommRing Rg] {k : ℕ}
end Uniq
end PI.OddDualWeyl


