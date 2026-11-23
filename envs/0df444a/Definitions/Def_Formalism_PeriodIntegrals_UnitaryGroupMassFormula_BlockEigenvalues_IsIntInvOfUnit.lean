-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_IsIntInvOfUnit
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_IsIntInvOfUnit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:31.953847+00:00
-- url     : https://prove2.me/theorems/f1e03c73-3aeb-44f5-a3ab-4b497c2e2add
-- title:
--   Is Int Inv Of Unit
-- statement:
--   Definitions and structural lemmas for Is Int Inv Of Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/IsIntInvOfUnit.lean

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace PI.DatumBlockEigen.Unit
variable {F : Type} [Field F] (O : Subring F) (ϖ : F)
def liftO {m n : Type} (N : Matrix m n F) (h : ∀ i j, N i j ∈ O) : Matrix m n O :=
  Matrix.of fun i j => ⟨N i j, h i j⟩
abbrev pI (hϖ : ϖ ∈ O) : Ideal O := Ideal.span {(⟨ϖ, hϖ⟩ : O)}
variable {O ϖ}
end PI.DatumBlockEigen.Unit


