-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:45:50.507326+00:00
-- url     : https://prove2.me/theorems/f258ae0a-73ca-4b07-b663-242d68de0154
-- title:
--   Of Fn Prod Int Cast
-- statement:
--   Definitions and structural lemmas for Of Fn Prod Int Cast, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerProductCast/OfFnProdIntCast.lean

import Definitions.Def_Formalism_PeriodIntegrals_QmStar
import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
noncomputable section
namespace PI.UnitaryGroupMassFormula.QmStar
def conjRev (t : ℕ) : Equiv.Perm (Fin t) ≃ Equiv.Perm (Fin t) where
  toFun σ := Fin.revPerm * σ * Fin.revPerm
  invFun σ := Fin.revPerm * σ * Fin.revPerm
  left_inv σ := Equiv.ext fun i => by simp [Equiv.Perm.mul_apply]
  right_inv σ := Equiv.ext fun i => by simp [Equiv.Perm.mul_apply]
end PI.UnitaryGroupMassFormula.QmStar


