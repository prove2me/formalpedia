-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementW
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementW
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T21:10:35.66469+00:00
-- url     : https://prove2.me/theorems/6d776130-1c01-4f3b-80fe-18cffde5cb10
-- title:
--   Statement W
-- statement:
--   Definitions and structural lemmas for Statement W, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/StatementW.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementJ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_CurveHyp
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
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.L2.Th1.A (fgl iSer logSer wpReg g₂ g₃ IntModel)
section Defs
variable {K : Type} [Field K] [CharZero K]
def sgW (W : WeierstrassCurve K) (s2 : K) : PowerSeries K := sgStar s2 (wpReg W)
def phW (W : WeierstrassCurve K) (s2 : K) : PowerSeries K := phO s2 (wpReg W) (logSer W)
def beW (W : WeierstrassCurve K) (s2 : K) : MvPowerSeries (Fin 2) K := cob (fgl W) (phW W s2)
def e1W (W : WeierstrassCurve K) (xT : K) : K := xT + W.b₂ / 12
def kapW (W : WeierstrassCurve K) (xT : K) : K := 3 * e1W W xT ^ 2 - g₂ W / 4
def evenSigmaLogAtTwoTorsion (W : WeierstrassCurve K) (s2 xT : K) : PowerSeries K :=
  phE s2 (e1W W xT) (kapW W xT) (wOf (e1W W xT) (wpReg W)) (logSer W)
end Defs
def CurveSigma : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (s2 : K),
    PowerSeries.constantCoeff (phW W s2) = 0 ∧
    PowerSeries.subst (logSer W) (sgW W s2) = PowerSeries.X * fExp (-phW W s2) ∧
    MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * (atS (sgW W s2) * atD (sgW W s2)) =
      at1 0 (sgW W s2) ^ 2 * at1 1 (sgW W s2) ^ 2 * wpDiff (wpReg W)
def CurvePar : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K) (s2 : K),
    IntModel W →
    Simeq (par (fgl W) (iSer W) (phW W s2)) 0 ∧
    Simeq (ι := Unit) (PowerSeries.subst (iSer W) (phW W s2)) (phW W s2) ∧
    Simeq (ι := Unit)
      (MvPowerSeries.subst ![(PowerSeries.X : PowerSeries K), PowerSeries.X] (beW W s2))
      (2 * phW W s2) ∧
    ∀ (n : ℤ) (N : PowerSeries K), PowerSeries.constantCoeff N = 0 →
      PowerSeries.subst N (logSer W) = PowerSeries.C (n : K) * logSer W →
      Simeq (ι := Unit) (PowerSeries.subst N (phW W s2)) (((n ^ 2 : ℤ) : PowerSeries K) * phW W s2)
def WeierstrassBiadditiveModEquiv : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K) (s2 : K),
    IntModel W → ‖(2 : K)‖ = 1 →
    DivAB (beW W s2) ∧ swap2 (beW W s2) = beW W s2 ∧
      Simeq (d1 (fgl W) (beW W s2)) 0 ∧ Simeq (d1 (fgl W) (swap2 (beW W s2))) 0
def CurveJets : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K) (s2 : K),
    IntModel W → ‖(2 : K)‖ = 1 →
    ∀ n : ℕ, n = 1 ∨ 3 ≤ n →
      ‖PowerSeries.constantCoeff ((Dinv (logSer W))^[n] (phW W s2))‖ ≤ 1
def CurveTwo : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K)
    (s2 xT yT : K), IntModel W → W.toAffine.Equation xT yT → 2 * yT + W.a₁ * xT + W.a₃ = 0 →
    ‖xT‖ ≤ 1 → ‖yT‖ ≤ 1 →
    kapW W xT = 3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT ∧
    4 * e1W W xT ^ 3 - g₂ W * e1W W xT - g₃ W = 0 ∧
    PowerSeries.subst (iSer W) (evenSigmaLogAtTwoTorsion W s2 xT) = evenSigmaLogAtTwoTorsion W s2 xT ∧
    Simeq (par (fgl W) (iSer W) (evenSigmaLogAtTwoTorsion W s2 xT)) 0 ∧
    Simeq (ι := Unit) (2 * evenSigmaLogAtTwoTorsion W s2 xT) (2 * phW W s2)
def CurveTwoOdd : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K)
    (s2 xT yT : K), IntModel W → W.toAffine.Equation xT yT → 2 * yT + W.a₁ * xT + W.a₃ = 0 →
    ‖xT‖ ≤ 1 → ‖yT‖ ≤ 1 → ‖(2 : K)‖ = 1 →
    Simeq (ι := Unit) (evenSigmaLogAtTwoTorsion W s2 xT) (phW W s2) ∧
    DivAB (cob (fgl W) (evenSigmaLogAtTwoTorsion W s2 xT)) ∧
    Simeq (d1 (fgl W) (cob (fgl W) (evenSigmaLogAtTwoTorsion W s2 xT))) 0 ∧
    Simeq (d1 (fgl W) (swap2 (cob (fgl W) (evenSigmaLogAtTwoTorsion W s2 xT)))) 0
end Formalism.L2.Th1.B


