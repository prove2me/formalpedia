-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:53.680164+00:00
-- url     : https://prove2.me/theorems/5111bb6b-f275-49d0-882d-d32b3ff78d26
-- title:
--   Exists Oe Perm
-- statement:
--   Definitions and structural lemmas for Exists Oe Perm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/ExistsOePerm.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace PI.IsoDerivBFintype
instance finiteOE (h n : ℕ) : Finite (Fin h ↪o Fin n) :=
  Finite.of_injective (fun f : Fin h ↪o Fin n => (f : Fin h → Fin n)) DFunLike.coe_injective
instance fintypeOE (h n : ℕ) : Fintype (Fin h ↪o Fin n) := Fintype.ofFinite _
end PI.IsoDerivBFintype


