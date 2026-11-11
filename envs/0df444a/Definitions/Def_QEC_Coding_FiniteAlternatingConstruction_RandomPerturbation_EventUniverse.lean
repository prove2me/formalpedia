-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T22:44:41.403642+00:00
-- url     : https://prove2.me/theorems/66914a74-669e-4a0b-a767-220abe891a1a
-- title:
--   Event Universe
-- statement:
--   Definitions and structural lemmas for Event Universe, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventUniverse.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EligibleListQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedScan
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
noncomputable def rawEventUniverseQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) : List (Event P J r) × ℕ :=
  let tuples := fourTuplesQuery (triangleInputList P)
  let events := filterMapQuery (candidateEventQuery P J hr) tuples.1
  (events.1,tuples.2+events.2)
noncomputable def eventEqQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e f : Event P J r) : Bool × ℕ :=
  let forward := eventCompareQuery P J r e f
  let backward := eventCompareQuery P J r f e
  (forward.1 && backward.1,forward.2+backward.2+1)
noncomputable def eventUniverseQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) : List (Event P J r) × ℕ :=
  let raw := rawEventUniverseQuery P J hr
  let unique := dedupQuery (eventEqQuery P J r) raw.1
  let sorted := sortQuery (eventCompareQuery P J r) unique.1
  (sorted.1,raw.2+unique.2+sorted.2)
end QEC.Coding.BDL26RandomPerturbation


