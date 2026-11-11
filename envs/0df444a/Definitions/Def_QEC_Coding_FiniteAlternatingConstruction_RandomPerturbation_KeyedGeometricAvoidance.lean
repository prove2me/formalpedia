-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T04:43:52.397804+00:00
-- url     : https://prove2.me/theorems/08f37d23-9a32-43ba-89d3-085f928657e6
-- title:
--   Keyed Geometric Avoidance
-- statement:
--   Definitions and structural lemmas for Keyed Geometric Avoidance, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricAvoidance.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricProbability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodAssignments
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
set_option autoImplicit false
namespace QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory
noncomputable def KeyAvoid (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) : Set (Vertex P → Space) :=
  avoid (localEvent (keySupport P key hk J (anchorRadius p.m))
    (keyBad P key hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))) Finset.univ
noncomputable def KeyGood (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) : Set (Vertex P → Space) :=
  geometricSupport P p ∩ KeyAvoid P key hk J p
end QEC.Coding.BDL26KeyedGeometric


