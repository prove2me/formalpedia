-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_DifferenceLinearCoeff
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_DifferenceLinearCoeff
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T04:28:43.13832+00:00
-- url     : https://prove2.me/theorems/f0fd9415-f3f4-4d86-8f77-8dffc87e3a7f
-- title:
--   Difference Linear Coeff
-- statement:
--   Definitions and structural lemmas for Difference Linear Coeff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/DifferenceLinearCoeff.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementQ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
namespace Formalism.L2.Th1.A
namespace Q1
open CubeR
local notation "cc" => MvPowerSeries.constantCoeff
section Diag
variable {R : Type u} [CommRing R]
end Diag
section Diff
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
end Diff
end Q1
open Q1 CubeR
end Formalism.L2.Th1.A


