-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CoherentChooserSpecification_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13CoherentChooserSpecification_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T22:35:30.618888+00:00
-- url     : https://prove2.me/theorems/9fdea2cb-c67f-4e83-a2ab-efcc71f757d8
-- title:
--   FLT.Assumptions.MazurProof.N13CoherentChooserSpecification source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13CoherentChooserSpecification

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13CoherentChooserSpecification
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RationalCurvePointPicardRealization_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InverseInfinityWitnessClass_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CoherentChartComparison_p0

set_option autoImplicit false




/-!
Source pin: a6290bc36c3549d89239da82b13b1f59ebd0388e.
Candidate SPECIFICATION only. Lean elaboration / build / axiom checks: NOT RUN.
The imported candidate must be installed under FLT/Assumptions/MazurProof/.
No existence result for this structure is proved here.
-/
namespace MazurProof.N13CoherentChooserSpecification
noncomputable section

abbrev G := N13RationalPointEndgame.G
abbrev Data := N13TwoChartPicardRealization.Data

/-- Pointwise realization and geometric compatibility with rational points.
No additive law for the special code occurs in this specification. -/
structure Chooser where
  choose : G → Data
  generic_eq : ∀ P, (choose P).toGenericPic = N13InfinityBaseChange.picMapRatToQ₂ P
  saturated : ∀ P, N13TwoChartPicardRealization.AffineVerticallySaturated (choose P).charts
  point_compatible : ∀ P : N13RationalPointEndgame.RationalCurvePoint,
    Nonempty (N13CoherentChartComparison.IntegralComparison
      (choose (N13RationalPointEndgame.rationalAbel P)).charts
      (N13RationalCurvePointPicardRealization.data P).realization.charts)

/-- The separate geometric tensor-normalization obligation. A proof must
produce four actual regular functions for every P,Q, with nonzero reductions,
matching principal ideal equations and one common overlap fraction.
This is a target to prove, not an assumed substitute for the end theorem. -/
def HasIntegralTensorComparisons (c : Chooser) : Prop :=
  ∀ P Q : G, Nonempty (N13CoherentChartComparison.IntegralComparison
    (N13TwoChartLineTensor.tensor (c.choose P).charts (c.choose Q).charts)
    (N13TwoChartLineTensor.tensor (c.choose (P + Q)).charts (c.choose 0).charts))

/-- Precise combined existence target; deliberately a proposition definition,
not a theorem or a postulate. Its proof is missing. -/
def GlobalExistenceTarget : Prop :=
  ∃ c : Chooser, HasIntegralTensorComparisons c ∧
    c.choose 0 = N13InfinityPointPicardRealization.infinityPlusData ∧
    c.choose (N13Arithmetic.AJ13 N13Arithmetic.T) =
      N13InfinityPointPicardRealization.infinityMinusData ∧
    c.choose (-N13Arithmetic.AJ13 N13Arithmetic.T) =
      N13InverseInfinityWitness.inverseInfinityData

end
end MazurProof.N13CoherentChooserSpecification


