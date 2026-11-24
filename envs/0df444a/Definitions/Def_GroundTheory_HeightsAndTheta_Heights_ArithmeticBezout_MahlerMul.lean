-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:17.859805+00:00
-- url     : https://prove2.me/theorems/52471605-c811-4628-a349-c09d3e69c873
-- title:
--   Mahler Mul
-- statement:
--   Definitions and structural lemmas for Mahler Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/MahlerMul.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
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
open MeasureTheory Set MvPolynomial
noncomputable section
namespace LogInt
variable {n k : ℕ}
def ballSet (h : HermNorm n) (k : ℕ) : Set (Fin k × Fin n → ℂ) :=
  {u | ∀ i, h.norm (fun j => u (i, j)) < 1}
end LogInt
end
end GroundTheory.Heights₂.Heights


