-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EligibilityQuery
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EligibilityQuery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T03:05:50.975662+00:00
-- url     : https://prove2.me/theorems/9db0cdc0-3054-4177-becb-97bb33819ce5
-- title:
--   Eligibility Query
-- statement:
--   Definitions and structural lemmas for Eligibility Query, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EligibilityQuery.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace
noncomputable def triangleLabelEqQuery (P : TannerSquarePresentation) (a b : Triangle P) : Bool × ℕ :=
  let A := indexQuery a (triangleInputList P)
  let B := indexQuery b (triangleInputList P)
  (decide (A.1 = B.1),A.2+B.2+1)
noncomputable def colorMatchQuery (P : TannerSquarePresentation) (a b : Triangle P) : Bool × ℕ :=
  let A := triangleColorQuery P a
  let B := triangleColorQuery P b
  let q := listAllQuery (fun i : Fin 3 => (decide (A.1 i = B.1 i),1)) [0,1,2]
  (q.1,A.2+B.2+q.2)
noncomputable def anchorCloseProgram : RealTest :=
  let d := subExpr (smulExpr (.constant (1/2)) centerExpr)
    (smulExpr (.constant (1/2)) (vertexExpr 0))
  .le (dotExpr d d) (.mul .radius .radius)
noncomputable def anchorCloseQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (a b : Triangle P) : Bool × ℕ :=
  anchorCloseProgram.run (fun _ => J (.x (P.faceX b.1))) (J (.x (P.faceX a.1))) radius
noncomputable def eligiblePairQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (a b : Triangle P) : Bool × ℕ :=
  let color := colorMatchQuery P a b
  let close := anchorCloseQuery P J r a b
  (color.1 && close.1,color.2+close.2+1)
end QEC.Coding.BDL26RandomPerturbation


