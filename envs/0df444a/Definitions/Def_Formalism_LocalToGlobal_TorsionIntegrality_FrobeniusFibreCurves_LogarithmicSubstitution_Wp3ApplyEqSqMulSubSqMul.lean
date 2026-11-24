-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_Wp3ApplyEqSqMulSubSqMul
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_Wp3ApplyEqSqMulSubSqMul
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T21:49:29.438827+00:00
-- url     : https://prove2.me/theorems/223a67ed-3339-4a76-b3a5-21b1ac07c940
-- title:
--   Wp3 Apply Eq Sq Mul Sub Sq Mul
-- statement:
--   Definitions and structural lemmas for Wp3 Apply Eq Sq Mul Sub Sq Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/Wp3ApplyEqSqMulSubSqMul.lean

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
namespace Formalism.L2.Th1.B.Det
open Formalism.InvariantFactorPaths.G7 (at1)
section
variable {K : Type} [Field K] [CharZero K]
local notation "A3" => MvPowerSeries (Fin 3) K
def Xt (P : PowerSeries K) (j : Fin 3) : A3 := 1 + MvPowerSeries.X j ^ 2 * at1 j P
def Yt (P : PowerSeries K) (j : Fin 3) : A3 := -2 + MvPowerSeries.X j ^ 3 * at1 j (dz P)
def dXt (P : PowerSeries K) (j : Fin 3) : A3 :=
  2 * MvPowerSeries.X j * at1 j P + MvPowerSeries.X j ^ 2 * at1 j (dz P)
def dYt (P : PowerSeries K) (j : Fin 3) : A3 :=
  3 * MvPowerSeries.X j ^ 2 * at1 j (dz P) + MvPowerSeries.X j ^ 3 * at1 j (dz (dz P))
end
end Formalism.L2.Th1.B.Det


