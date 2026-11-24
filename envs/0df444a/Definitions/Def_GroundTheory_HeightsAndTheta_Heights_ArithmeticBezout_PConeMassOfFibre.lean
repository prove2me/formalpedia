-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:43.934888+00:00
-- url     : https://prove2.me/theorems/ae0b71eb-ec7f-4605-9656-c6fc2c27506b
-- title:
--   PCone Mass Of Fibre
-- statement:
--   Definitions and structural lemmas for PCone Mass Of Fibre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section
def coordPlaneSubst (m k : ℕ) : Fin (m + k) → MvPolynomial (Fin m) ℂ :=
  Fin.append (fun i => X i) (fun _ => 0)
def coordPlaneIdeal (m k : ℕ) : Ideal (MvPolynomial (Fin (m + k)) ℂ) :=
  RingHom.ker (aeval (coordPlaneSubst m k))
def coordPlaneBlock {m k : ℕ} (π : Fin m → Fin (m + k) → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => π i (Fin.castAdd k j)
def coordPlaneDetPoly (m k : ℕ) : MvPolynomial (Fin m × Fin (m + k)) ℂ :=
  (Matrix.of fun i j : Fin m => (X (i, Fin.castAdd k j) : MvPolynomial (Fin m × Fin (m + k)) ℂ)).det
end
end GroundTheory.Heights₂.Heights


