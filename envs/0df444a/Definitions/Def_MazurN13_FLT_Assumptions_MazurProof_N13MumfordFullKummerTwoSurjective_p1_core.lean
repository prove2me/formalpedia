-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordFullKummerTwoSurjective_p1_core
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13MumfordFullKummerTwoSurjective_p1_core
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T15:01:24.100786+00:00
-- url     : https://prove2.me/theorems/720d09d8-52dc-4372-bf0a-df2b076406a8
-- title:
--   FLT.Assumptions.MazurProof.N13MumfordFullKummerTwoSurjective full-gauge constructor
-- statement:
--   A full Kummer identity for a point supplies the same chosen representative, finite ideal square root, and half used by the global construction.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13MumfordFullKummerTwoSurjective

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13MumfordFullKummerTwoSurjective
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordFullKummerTwoSurjective_p0

set_option autoImplicit false

namespace MazurProof.N13MumfordFullKummerTwoSurjective
noncomputable section
/-- Construct the original chosen generic half from its full-gauge witness.
The representative, coordinate choices, ideal root, and half are retained. -/
def constructedHalfDataOfFullGauge (P : G)
    (hfull : N13MumfordOrientedFullKummer.orientedFullKummer P = 1) :
    ConstructedHalfData P := by
  let D := N13LowDegreeKummerHom.representative P
  let hcoordinates :=
    (N13MumfordFullKummerIdentityFiber.orientedFullKummer_eq_one_iff_exists_coordinates
      P).mp hfull
  let β := Classical.choose hcoordinates
  let hq := Classical.choose_spec hcoordinates
  let q := Classical.choose hq
  have hcoordinates_spec := Classical.choose_spec hq
  let root :=
    N13MumfordFullKummerIdentityFiber.finiteIdealGraphRootData_of_full_gauge
      D β q hcoordinates_spec.1 hcoordinates_spec.2
  let finite :=
    N13MumfordFullKummerIdentityFiber.finiteIdealHalfData
      D root
  refine
    { representative := D
      representative_spec :=
        N13LowDegreeKummerHom.lowClass_representative P
      finite := finite
      double_eq := ?_ }
  exact
    (N13LowDegreeKummerHom.lowClass_representative P).symm.trans
      finite.half_spec


end
end MazurProof.N13MumfordFullKummerTwoSurjective


