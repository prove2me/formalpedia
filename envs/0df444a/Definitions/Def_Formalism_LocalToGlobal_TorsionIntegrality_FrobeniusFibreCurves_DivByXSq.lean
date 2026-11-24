-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_DivByXSq
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_DivByXSq
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T21:10:08.086218+00:00
-- url     : https://prove2.me/theorems/4adeff50-a966-4bb0-b5b4-d47b10482d6f
-- title:
--   Div By XSq
-- statement:
--   Definitions and structural lemmas for Div By XSq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/DivByXSq.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LawDifferenceThree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Th1.B
open Formalism.InvariantFactorPaths.G7 (at1 cob d1 in3 swap2 DivAB)
section Alg
variable {K : Type} [Field K] [CharZero K]
def divByXSq (w : PowerSeries K) : PowerSeries K := PowerSeries.mk fun n => PowerSeries.coeff (n + 2) w
def sW (w : PowerSeries K) : PowerSeries K :=
  PowerSeries.X * fExp (PowerSeries.C (1 / 2 : K) * fLog (divByXSq w))
def gT (ep : PowerSeries K) (xT : K) : PowerSeries K := ep - PowerSeries.C xT * PowerSeries.X ^ 2
def thT (ep : PowerSeries K) (xT yT : K) : PowerSeries K :=
  (ep + PowerSeries.C yT * PowerSeries.X ^ 3) * (gT ep xT)⁻¹
def LT (ep : PowerSeries K) (xT yT a1 : K) : MvPowerSeries (Fin 2) K :=
  MvPowerSeries.X 1 * at1 0 (thT ep xT yT) + MvPowerSeries.X 0 * at1 1 (thT ep xT yT) -
    MvPowerSeries.C a1 * MvPowerSeries.X 0 * MvPowerSeries.X 1
def thZ (s2 e1 kap : K) (w : PowerSeries K) : PowerSeries K :=
  sigma1 e1 kap w * fExp (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2))
end Alg
section Norm
open Formalism.DworkPowerSeriesWeights (Integral)
variable {K : Type} [NormedField K] [CharZero K]
def TwoHyp (g2 g3 c0 a1 a3 xT yT : K) : Prop :=
  2 * yT + a1 * xT + a3 = 0 ∧ 4 * (xT + c0) ^ 3 - g2 * (xT + c0) - g3 = 0 ∧
    ‖xT‖ ≤ 1 ∧ ‖yT‖ ≤ 1 ∧ ‖a1‖ ≤ 1 ∧ ‖3 * (xT + c0) ^ 2 - g2 / 4‖ ≤ 1
end Norm
end Formalism.L2.Th1.B


