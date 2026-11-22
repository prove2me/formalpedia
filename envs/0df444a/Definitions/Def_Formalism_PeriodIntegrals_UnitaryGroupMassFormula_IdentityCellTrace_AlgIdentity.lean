-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdentityCellTrace_AlgIdentity
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdentityCellTrace_AlgIdentity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:46:03.916279+00:00
-- url     : https://prove2.me/theorems/166e32aa-384b-4e80-8f84-d14002b96872
-- title:
--   Alg Identity
-- statement:
--   Definitions and structural lemmas for Alg Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdentityCellTrace/AlgIdentity.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdentityCellTrace_ExistsSmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
namespace PI.UnitaryGroupMassFormula.IdCellInSW
section Alg
variable {E : Type} [Field E] [StarRing E] {r : ℕ}
end Alg
variable {E : Type} [Field E] [NumberField E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
end PI.UnitaryGroupMassFormula.IdCellInSW


