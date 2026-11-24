-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:31.597641+00:00
-- url     : https://prove2.me/theorems/519198a5-2be1-4dab-a99e-bd41f9d4adff
-- title:
--   Line Inhabitant
-- statement:
--   Definitions and structural lemmas for Line Inhabitant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LineInhabitant.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace LineChowForm
variable {F : Type*} [Field F]
variable {F : Type*} [Field F]
def D2 : MvPolynomial (Fin 2 × Fin 2) F := X (0,0) * X (1,1) - X (0,1) * X (1,0)
def substZeroZeroZero : MvPolynomial (Fin 2 × Fin 2) F →ₐ[F] MvPolynomial (Fin 2 × Fin 2) F :=
  aeval (fun ij => if ij = ((0 : Fin 2),(0 : Fin 2)) then 0 else X ij)
def substZeroOneOne : MvPolynomial (Fin 2 × Fin 2) F →ₐ[F] MvPolynomial (Fin 2 × Fin 2) F :=
  aeval (fun ij => if ij = ((1 : Fin 2),(1 : Fin 2)) then 0 else X ij)
end LineChowForm
end
end GroundTheory.Heights₂.Heights


