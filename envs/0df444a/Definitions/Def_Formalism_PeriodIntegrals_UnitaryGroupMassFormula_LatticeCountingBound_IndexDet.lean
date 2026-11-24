-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDet
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDet
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T13:54:35.344706+00:00
-- url     : https://prove2.me/theorems/0ac1d227-2ca2-48fc-ab13-d3580a79d4bd
-- title:
--   Index Det
-- statement:
--   Definitions and structural lemmas for Index Det, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/IndexDet.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
open NumberField Matrix
namespace PI.UnitaryGroupMassFormula.LCG
namespace DetIdxW
variable {K : Type} [Field K] [NumberField K] {k : ℕ}
def ιc (K : Type) [Field K] [NumberField K] (k : ℕ) : (Fin k → 𝓞 K) →+ (Fin k → K) :=
  (LinearMap.compLeft (Algebra.linearMap (𝓞 K) K) (Fin k)).toAddMonoidHom
def vm (M : Matrix (Fin k) (Fin k) K) : (Fin k → K) →+ (Fin k → K) where
  toFun s := s ᵥ* M
  map_zero' := Matrix.zero_vecMul M
  map_add' a b := by simp [Matrix.add_vecMul]
end DetIdxW
end PI.UnitaryGroupMassFormula.LCG


