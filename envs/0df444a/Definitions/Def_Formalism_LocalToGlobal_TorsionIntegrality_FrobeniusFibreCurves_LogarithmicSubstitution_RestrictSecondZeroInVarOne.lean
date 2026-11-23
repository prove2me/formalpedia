-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RestrictSecondZeroInVarOne
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RestrictSecondZeroInVarOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:03:12.448643+00:00
-- url     : https://prove2.me/theorems/89c4ac45-b999-4d5e-ad6e-41921a1fa18d
-- title:
--   Restrict Second Zero In Var One
-- statement:
--   Definitions and structural lemmas for Restrict Second Zero In Var One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RestrictSecondZeroInVarOne.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Th1.B.Add1
open Formalism.InvariantFactorPaths.G7 (at1)
section SlopeTestRemainingChoices
variable {K : Type} [Field K] [CharZero K]
def at1H {ι : Type} (x : ι) : PowerSeries K →ₐ[K] MvPowerSeries ι K :=
  PowerSeries.substAlgHom (PowerSeries.HasSubst.X x)
def ev0H : MvPowerSeries (Fin 2) K →ₐ[K] PowerSeries K :=
  MvPowerSeries.substAlgHom (a := ![(PowerSeries.X : PowerSeries K), 0])
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (by
      intro i; fin_cases i
      · exact PowerSeries.constantCoeff_X
      · exact map_zero _))
end SlopeTestRemainingChoices
end Formalism.L2.Th1.B.Add1


