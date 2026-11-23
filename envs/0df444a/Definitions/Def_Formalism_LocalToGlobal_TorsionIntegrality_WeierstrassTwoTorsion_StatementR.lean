-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementR
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:52.960803+00:00
-- url     : https://prove2.me/theorems/e1e3b28d-e306-4964-aba1-0f6abe59d647
-- title:
--   Statement R
-- statement:
--   Definitions and structural lemmas for Statement R, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/StatementR.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementQ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LawDifferenceThree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
namespace Formalism.L2.Th1.A
def WpPrimeInU : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    X ^ 3 * (-2 + logSer W ^ 3 * (derivative K (wpReg W)).subst (logSer W)) =
      logSer W ^ 3 * (-2 * xS W + C W.a₁ * X * xS W + C W.a₃ * X ^ 3)
def BridgeCurve3 : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    IntModel W →
    Formalism.L2.Th1.B.CurveHyp3 (fgl W) (logSer W) (wpReg W) (xS W) W.a₁ W.a₃
end Formalism.L2.Th1.A


