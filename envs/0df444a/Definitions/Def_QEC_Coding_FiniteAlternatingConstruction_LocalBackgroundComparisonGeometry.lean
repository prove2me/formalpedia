-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonGeometry
-- name    : QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonGeometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T14:32:30.774102+00:00
-- url     : https://prove2.me/theorems/9e2f5076-ff02-4bff-9e9b-70946688165c
-- title:
--   Local Background Comparison Geometry
-- statement:
--   Definitions and structural lemmas for Local Background Comparison Geometry, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonGeometry.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_QubitBallBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26LocalBackgroundComparisonGeometry
open Classical MeasureTheory ProbabilityTheory
open MultiscaleDecoder BDL26IndexedDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26LocalBackgroundComparisonResponse BDL26LocalBackgroundComparisonDepth
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26QubitBallBounds
open QEC.Coding.ProbabilisticConstruction.SphericalCap
def ChangesDefect (S : OddScale) (n : Nat) (g : W S n) (q : Q S n)
    (A : Finset (Q S n)) : Prop :=
  BDL26AllDepthBottomComparisonStability.residual S n
    (perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g)
    (canonicalBasisWord (F:=BDL26Field) q)-
  BDL26AllDepthBottomComparisonStability.residual S n
    (perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n)
      (backgroundRestriction S n g A)) (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S n
def responseLevel (t R : ℝ) : Nat := budgetDepth (ballBudget t R)+2
end QEC.Coding.BDL26LocalBackgroundComparisonGeometry


