-- Prove2me | Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
-- name    : HuangN13_PrimitiveAffineComparisonCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:07:27.853776+00:00
-- url     : https://prove2.me/theorems/9d556640-da4a-4aea-b80b-9668632bf840
-- title:
--   Affine vertical saturation and the generic ideal unit of a two-chart line
-- statement:
--   The original vertical-saturation predicate for the affine ideal of a line and its generic fractional-ideal unit, with no principal-comparison or additivity assumption added.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore

set_option autoImplicit false

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- An affine integral line lattice has no component supported purely over
the closed two-adic fibre.

Equivalently, multiplication by a nonzero scalar from `ℤ₂` can be cancelled
modulo the affine ideal.  This is the exact condition under which extension
to the generic fibre followed by contraction recovers the original lattice. -/
def AffineVerticallySaturated (L : Line) : Prop :=
  ∀ (r : N13IntegralModelContraction.R₂), r ≠ 0 →
    ∀ a : N13IntegralModelContraction.IntegralRing,
      algebraMap N13IntegralModelContraction.R₂
            N13IntegralModelContraction.IntegralRing r * a ∈ L.affineIdeal →
        a ∈ L.affineIdeal
end
end MazurProof.N13TwoChartPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Extension of the invertible affine ideal of a proper line to the generic
sextic coordinate ring. -/
def genericIdealUnit (L : Line) :
    Units N13IntegralFractionalHull.RationalFractionalIdeal :=
  Units.map
    N13IntegralFractionalHull.extendFractional.toMonoidHom
    L.affine_isUnit.unit
end
end MazurProof.N13TwoChartPicardRealization
end
end


