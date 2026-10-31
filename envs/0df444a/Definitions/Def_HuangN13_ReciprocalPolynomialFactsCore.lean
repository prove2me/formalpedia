-- Prove2me | Definitions.Def_HuangN13_ReciprocalPolynomialFactsCore
-- name    : HuangN13_ReciprocalPolynomialFactsCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-30T12:33:42.127072+00:00
-- url     : https://prove2.me/theorems/eac279bf-bc26-4d2d-90b9-d9d2f8ee8fb9
-- title:
--   Exact reciprocal polynomial facts used by the actual graph-line type
-- statement:
--   Exactly the original integralReciprocal_monic and integralReciprocal_natDegree proof commands. Their constants occur in the original actual twoChartLine arguments of the saturation statement; the original type is retained.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13ReciprocalQuadraticReflection
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem integralReciprocal_monic
    (a b : R₂) :
    (integralReciprocal a b).Monic := by
  unfold integralReciprocal
  monicity <;> norm_num
end
end MazurProof.N13ReciprocalQuadraticReflection
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13ReciprocalQuadraticReflection
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem integralReciprocal_natDegree
    (a b : R₂) :
    (integralReciprocal a b).natDegree = 2 := by
  unfold integralReciprocal
  compute_degree <;> norm_num
end
end MazurProof.N13ReciprocalQuadraticReflection
end
end


