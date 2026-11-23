-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementK
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementK
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:28.979793+00:00
-- url     : https://prove2.me/theorems/77ba8036-5ff6-4f42-a513-93ee89aecec6
-- title:
--   Statement K
-- statement:
--   Definitions and structural lemmas for Statement K, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/StatementK.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_CMGoodModels_Statement
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
def shortW {K : Type} [Field K] (g2 g3 : K) : WeierstrassCurve K :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -g2 / 4, a₆ := -g3 / 4 }
def ShortInv : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K),
    (shortW g2 g3).b₂ = 0 ∧ g₂ (shortW g2 g3) = g2 ∧ g₃ (shortW g2 g3) = g3 ∧
    (shortW g2 g3).Δ = g2 ^ 3 - 27 * g3 ^ 2
def WpNumEq : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K),
    Formalism.L2.Th1.CM.wpNum (g₂ W) (g₃ W) = 1 + X ^ 2 * wpReg W ∧
    Formalism.L2.Th1.CM.wpDen (g₂ W) (g₃ W) = 1 - C (1 / 2 : K) * X ^ 3 * derivative K (wpReg W)
def WpRegInv : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W W' : WeierstrassCurve K),
    g₂ W = g₂ W' → g₃ W = g₃ W' → wpReg W = wpReg W'
def USerEq : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K),
    Formalism.L2.Th1.CM.uSer g2 g3 = expSer (shortW g2 g3)
end Formalism.L2.Th1.A


