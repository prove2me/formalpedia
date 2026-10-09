-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpreadRationalPointReduction_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpreadRationalPointReduction_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T19:42:49.938755+00:00
-- url     : https://prove2.me/theorems/8ad2c14b-f708-40bb-afd9-6b51fd6c2d6d
-- title:
--   FLT.Assumptions.MazurProof.N13SpreadRationalPointReduction source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpreadRationalPointReduction

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpreadRationalPointReduction
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ProperCurveReduction_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpreadClassifier_p0

set_option autoImplicit false




/-!
# Assemble rational-point reduction from integral spreads

This is the thin geometric adapter between relation-first specialization
and the N13 rational-point endgame.  Its only point-specific hypothesis says
that the proper spread of a rational Abel divisor realizes the special Abel
class of the properly reduced point.
-/

namespace MazurProof.N13SpreadRationalPointReduction

noncomputable section

universe u

abbrev G : Type :=
  N13RationalPointEndgame.G

abbrev SpecialSet : Type :=
  N13RationalPointEndgame.SpecialSet

abbrev RationalCurvePoint : Type :=
  N13RationalPointEndgame.RationalCurvePoint

/-- Complete geometric data needed after the purely algebraic spread
classifier has been constructed. -/
structure Data (Line : Type u) where
  spread :
    N13SpreadClassifier.SpreadData G SpecialSet Line
  abel_reduces :
    ∀ P : RationalCurvePoint,
      spread.ReducesTo
        (N13RationalPointEndgame.rationalAbel P)
        (N13RationalPointEndgame.specialPointClass
          (N13ProperCurveReduction.reduceCurve P))

namespace Data

variable {Line : Type u} (D : Data Line)

/-- Relation-first proper specialization supplies exactly the semantic
package consumed by the already-proved rational-point endgame. -/
def compatibleReduction :
    N13RationalPointEndgame.CompatibleReduction where
  classifier := D.spread.classifierData
  reduceCurve := N13ProperCurveReduction.reduceCurve
  classify_abel := by
    intro P
    exact
      ((D.spread.reducesTo_iff_eq_classify
        (N13RationalPointEndgame.rationalAbel P)
        (N13RationalPointEndgame.specialPointClass
          (N13ProperCurveReduction.reduceCurve P))).mp
            (D.abel_reduces P)).symm
  reduce_cusp := N13ProperCurveReduction.reduceCurve_cusp

theorem curvePoint_eq_cusp
    (separated :
      N18RouteC.Separated.NSeparated
        D.compatibleReduction.classifier.red.ker 2)
    (P : RationalCurvePoint) :
    ∃ c : N13Mumford.Cusp13,
      P = N13Mumford.cuspPoint c :=
  D.compatibleReduction.curvePoint_eq_cusp separated P

theorem affine_x_is_cuspidal
    (separated :
      N18RouteC.Separated.NSeparated
        D.compatibleReduction.classifier.red.ker 2) :
    ∀ X Y : ℚ, N13CurveModel.C13SexticEq X Y →
      X = 0 ∨ X = -1 :=
  D.compatibleReduction.affine_x_is_cuspidal separated

end Data

end

end MazurProof.N13SpreadRationalPointReduction


