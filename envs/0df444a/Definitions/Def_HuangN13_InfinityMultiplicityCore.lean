-- Prove2me | Definitions.Def_HuangN13_InfinityMultiplicityCore
-- name    : HuangN13_InfinityMultiplicityCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-30T11:40:30.740105+00:00
-- url     : https://prove2.me/theorems/f75d3c22-0a0d-4b87-9c72-3c8faab24add
-- title:
--   Actual infinity multiplicities of a two-chart line
-- statement:
--   The original Line alias and the predicate equating its two actual expanded infinity ideals with the indicated powers. No additional statement data.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore

set_option autoImplicit false

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
abbrev Line := N13TwoChartPicardRealization.Line
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The actual completed generic infinity ideal, with both sheet orders. -/
def HasInfinityMultiplicities (L : Line) (p m : ℕ) : Prop :=
  Ideal.map positiveExpansion L.infinityIdeal =
      Ideal.span ({PowerSeries.X ^ p} : Set QP) ∧
  Ideal.map negativeExpansion L.infinityIdeal =
      Ideal.span ({PowerSeries.X ^ m} : Set QP)
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end


