-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExecutionPrimitiveQueries
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExecutionPrimitiveQueries
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T22:46:14.563896+00:00
-- url     : https://prove2.me/theorems/acd457ea-c33c-4c5b-890a-b680720c755f
-- title:
--   Execution Primitive Queries
-- statement:
--   Definitions and structural lemmas for Execution Primitive Queries, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExecutionPrimitiveQueries.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedSteps
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
noncomputable def vertexInputList (P : TannerSquarePresentation) : List (Vertex P) :=
  List.ofFn (Fintype.equivFin (Vertex P)).symm
noncomputable def initialRowsQuery (P : TannerSquarePresentation)
    (T : Table (X := fun _ : Vertex P => Space)) : List (Vertex P × ℕ × Space) × ℕ :=
  mapQuery (fun v => ((v,0,T (v,0)),4)) (vertexInputList P)
noncomputable def supportListQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : Event P J r) : List (Vertex P) × ℕ := by
  classical
  let raw := flatMapQuery (fun t : Triangle P =>
    ([triangleVertex P t 0,triangleVertex P t 1,triangleVertex P t 2],6)) e.val.toList
  let unique := dedupQuery (fun v w : Vertex P => (decide (v=w),1)) raw.1
  exact (unique.1,raw.2+unique.2)
noncomputable def outputRowsQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (p : Vertex P → Space) : List (Vertex P × Space) × ℕ :=
  mapQuery (fun v => let q := pointSnapshotQuery lambda (J v) (p v)
                     ((v,q.1),q.2+3)) (vertexInputList P)
end QEC.Coding.BDL26RandomPerturbation


