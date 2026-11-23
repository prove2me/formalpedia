-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LastDiagMulVec
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LastDiagMulVec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:28:13.175125+00:00
-- url     : https://prove2.me/theorems/b258e6cd-1bc2-46e8-a295-437c67b5f143
-- title:
--   Last Diag Mul Vec
-- statement:
--   Definitions and structural lemmas for Last Diag Mul Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LastDiagMulVec.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ZeroOfBlk
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
namespace Formalism.L2.S.L6.UnitaryStandardVectors
variable {r : ℕ}
def lastDiag (t : ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun i j => if i = Fin.last r ∧ j = Fin.last r then t else 0
end Formalism.L2.S.L6.UnitaryStandardVectors


