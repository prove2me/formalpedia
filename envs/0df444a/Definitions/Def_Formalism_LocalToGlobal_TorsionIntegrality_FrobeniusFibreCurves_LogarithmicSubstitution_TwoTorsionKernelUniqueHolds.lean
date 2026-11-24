-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_TwoTorsionKernelUniqueHolds
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_TwoTorsionKernelUniqueHolds
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T22:37:17.18484+00:00
-- url     : https://prove2.me/theorems/b89c3fb3-0e50-403b-a023-3bfda8a10e9d
-- title:
--   Two Torsion Kernel Unique Holds
-- statement:
--   Definitions and structural lemmas for Two Torsion Kernel Unique Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/TwoTorsionKernelUniqueHolds.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Th1.B.KNorm
open Formalism.ELL (InFormalGroupPoints)
open Formalism.L2.Th1.E (px py IntCurve)
open WeierstrassCurve.Affine (Point)
section Norm
variable {K : Type} [NormedField K] [IsUltrametricDist K]
variable {b2 b4 b6 b8 x : K}
end Norm
section Curve
variable {K : Type} [Field K] {W : WeierstrassCurve K} {x y : K}
variable [DecidableEq K]
end Curve
section Main
variable {K : Type} [NormedField K] [IsUltrametricDist K] [DecidableEq K]
  {W : WeierstrassCurve K}
end Main
end Formalism.L2.Th1.B.KNorm


