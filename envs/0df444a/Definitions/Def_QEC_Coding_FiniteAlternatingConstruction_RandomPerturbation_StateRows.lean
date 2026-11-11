-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateRows
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateRows
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T22:50:19.171671+00:00
-- url     : https://prove2.me/theorems/81042761-cc6c-4468-a768-5cfba09e317c
-- title:
--   State Rows
-- statement:
--   Definitions and structural lemmas for State Rows, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateRows.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExecutionPrimitiveQueries
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
abbrev StateRows (P : TannerSquarePresentation) := List (Vertex P × ℕ × Space)
variable {P : TannerSquarePresentation}
noncomputable def stateRowQuery (v : Vertex P) : StateRows P → (ℕ × Space) × ℕ
  | [] => ((0,0),0)
  | row::L => if row.1=v then (row.2,2) else
      let q := stateRowQuery v L
      (q.1,q.2+2)
noncomputable def statePoints (R : StateRows P) (v : Vertex P) : Space := (stateRowQuery v R).1.2
def StateRowsRep (P : TannerSquarePresentation) (T : Table (X := fun _ : Vertex P => Space))
    (c : Counters (Vertex P)) (R : StateRows P) : Prop :=
  R.map Prod.fst = vertexInputList P ∧ ∀ row ∈ R, row.2 = (c row.1,T (row.1,c row.1))
noncomputable def refreshStateRowQuery (support : List (Vertex P))
    (T : Table (X := fun _ : Vertex P => Space)) (row : Vertex P × ℕ × Space) :
    (Vertex P × ℕ × Space) × ℕ :=
  let member := memberQuery (fun v w : Vertex P => (decide (v=w),1)) row.1 support
  (if member.1 then (row.1,row.2.1+1,T (row.1,row.2.1+1)) else row,member.2+6)
noncomputable def refreshStateRowsQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : Event P J r) (T : Table (X := fun _ : Vertex P => Space)) (R : StateRows P) : StateRows P × ℕ :=
  let support := supportListQuery P J r e
  let update := mapQuery (refreshStateRowQuery support.1 T) R
  (update.1,support.2+update.2)
noncomputable def outputStateRowsQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (R : StateRows P) : List (Vertex P × Space) × ℕ :=
  mapQuery (fun row => let q := pointSnapshotQuery lambda (J row.1) row.2.2
                       ((row.1,q.1),q.2+3)) R
end QEC.Coding.BDL26RandomPerturbation


