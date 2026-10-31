-- Prove2me | Definitions.Def_HuangN13_FiniteInfinityClosureCore
-- name    : HuangN13_FiniteInfinityClosureCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-30T11:40:30.442505+00:00
-- url     : https://prove2.me/theorems/4bc25297-b95d-4f78-9111-801301e9e498
-- title:
--   The actual infinity-chart closure of an affine ideal
-- statement:
--   The original infinityClosure definition: extend an affine ideal to the ordinary overlap, then contract it to the infinity chart. Exactly one original definition command.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore

set_option autoImplicit false

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13FiniteAffineTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The infinity-chart closure of an affine ideal is obtained by restricting
to the ordinary overlap and contracting back to the infinity chart. -/
def infinityClosure
    (I : Ideal AffineCurve) : Ideal InfinityCurve :=
  (Ideal.map
      N13OrdinaryCurveOverlap.affineToInfinityOverlap I).under
    InfinityCurve
end
end MazurProof.N13FiniteAffineTwoChart
end
end
end


