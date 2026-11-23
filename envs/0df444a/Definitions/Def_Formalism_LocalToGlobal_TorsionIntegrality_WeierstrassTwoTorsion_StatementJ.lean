-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementJ
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementJ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:10.839407+00:00
-- url     : https://prove2.me/theorems/9ce20d46-63a1-427a-9a26-f9d713c02b31
-- title:
--   Statement J
-- statement:
--   Definitions and structural lemmas for Statement J, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/StatementJ.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_CurveHyp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
namespace Formalism.L2.Th1.A
def IntModel {K : Type} [NormedField K] (W : WeierstrassCurve K) : Prop :=
  ‖W.a₁‖ ≤ 1 ∧ ‖W.a₂‖ ≤ 1 ∧ ‖W.a₃‖ ≤ 1 ∧ ‖W.a₄‖ ≤ 1 ∧ ‖W.a₆‖ ≤ 1
def BridgeWp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K),
    Formalism.L2.Th1.B.IsWp (g₂ W) (g₃ W) (wpReg W)
def BridgeLaw : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    IntModel W →
    Formalism.L2.Th1.B.LawLog (fgl W) (logSer W) ∧ Formalism.L2.Th1.B.IsInv (logSer W) (iSer W) ∧
    (‖(2 : K)‖ = 1 → Formalism.L2.Th1.B.IsHalf (logSer W) (halfSer W))
def BridgeCurve : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    IntModel W →
    Formalism.L2.Th1.B.CurveHyp (fgl W) (iSer W) (logSer W) (wpReg W) (xS W) (W.b₂ / 12)
def BridgeTwo : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K)
    (xT yT : K), W.toAffine.Equation xT yT → 2 * yT + W.a₁ * xT + W.a₃ = 0 →
    (tS W xT).subst (expSer W) = Formalism.L2.Th1.B.wOf (xT + W.b₂ / 12) (wpReg W) ∧
    Formalism.L2.Th1.B.IsW (3 * (xT + W.b₂ / 12)) (3 * (xT + W.b₂ / 12) ^ 2 - g₂ W / 4)
      ((tS W xT).subst (expSer W)) ∧
    (IntModel W → ‖xT‖ ≤ 1 → Formalism.DworkPowerSeriesWeights.Integral (ι := Unit) (tS W xT))
end Formalism.L2.Th1.A


