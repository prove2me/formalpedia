-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T21:48:55.469461+00:00
-- url     : https://prove2.me/theorems/2d031e5e-d0fe-4f6d-8d65-b7e67556bfa8
-- title:
--   Real Adelic Inert Transport Type Forms Eq Alt
-- statement:
--   Definitions and structural lemmas for Real Adelic Inert Transport Type Forms Eq Alt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RealAdelicInertTransportTypeFormsEqAlt.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Th1.B.Fs
open Formalism.InvariantFactorPaths.G7 (at1)
section
variable {K : Type} [Field K] [CharZero K]
local notation "A3" => MvPowerSeries (Fin 3) K
theorem hs_emb (j k : Fin 3) :
    MvPowerSeries.HasSubst ![(MvPowerSeries.X j : A3), MvPowerSeries.X k] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by fin_cases s <;> simp
def emb (j k : Fin 3) : MvPowerSeries (Fin 2) K →ₐ[K] A3 := MvPowerSeries.substAlgHom (hs_emb j k)
theorem hasSubst_eval_last_zero :
    MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : A3), MvPowerSeries.X 1, 0] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by fin_cases s <;> simp
def ev3H : A3 →ₐ[K] A3 := MvPowerSeries.substAlgHom hasSubst_eval_last_zero
end
end Formalism.L2.Th1.B.Fs


