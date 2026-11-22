-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_NormDetConjExp
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_NormDetConjExp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:14.415488+00:00
-- url     : https://prove2.me/theorems/9c3afdf9-c196-4ca5-948c-f8002aa4d10c
-- title:
--   Norm Det Conj Exp
-- statement:
--   Definitions and structural lemmas for Norm Det Conj Exp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped MatrixOrder ComplexOrder
noncomputable section
namespace PI.ET
namespace HornW
variable {n : ℕ}
def emb {k : ℕ} (hk : k ≤ n) : Matrix (Fin n) (Fin k) ℂ :=
  Matrix.of fun i j => if i = Fin.castLE hk j then 1 else 0
end HornW
end PI.ET


