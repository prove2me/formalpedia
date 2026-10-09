-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordFullKummerTwoSurjective_p1
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13MumfordFullKummerTwoSurjective_p1
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T17:21:13.813238+00:00
-- url     : https://prove2.me/theorems/733c4b5b-dc87-4488-98d4-a56ff1a59070
-- title:
--   FLT.Assumptions.MazurProof.N13MumfordFullKummerTwoSurjective source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13MumfordFullKummerTwoSurjective

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13MumfordFullKummerTwoSurjective
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianGlobalZeroCarrierDlog_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordFullKummerTwoSurjective_p1_core

set_option autoImplicit false

namespace MazurProof.N13MumfordFullKummerTwoSurjective
noncomputable section
/-- Apply the original global full-gauge proof to the retained constructor. -/
def constructedHalfData (P : G) :
    ConstructedHalfData P :=
  constructedHalfDataOfFullGauge P
    ((N13MumfordOrientedFullKummer.structuralKummer_eq_zero_iff_full_eq_one
      P).mp
        (N13GaussianGlobalZeroCarrierDlog.actualKummer_trivial P))

end
end MazurProof.N13MumfordFullKummerTwoSurjective


