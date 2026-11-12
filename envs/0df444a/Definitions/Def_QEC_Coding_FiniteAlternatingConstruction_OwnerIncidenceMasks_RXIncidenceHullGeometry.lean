-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGeometry
-- name    : QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGeometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T11:43:55.728024+00:00
-- url     : https://prove2.me/theorems/f28e68aa-96c1-4782-80a2-8be77dad9fde
-- title:
--   RXIncidence Hull Geometry
-- statement:
--   Definitions and structural lemmas for RXIncidence Hull Geometry, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGeometry.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_QubitBallBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRetainedGrowth
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RXIncidenceHullGeometry
open Classical MeasureTheory ProbabilityTheory
open MultiscaleDecoder BDL26IndexedDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26QubitBallBounds
open BDL26RXDifferentialMasks BDL26RXIncidenceHullRetainedGrowth
open QEC.Coding.ProbabilisticConstruction.SphericalCap
def hullLevel (B : Nat) : Nat := 2*(B+1)
def hullStep (B : Nat) : StepIndex (hullLevel B+1) := ⟨hullLevel B,by omega⟩
end QEC.Coding.BDL26RXIncidenceHullGeometry


