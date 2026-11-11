-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateEventQuery
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateEventQuery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T22:57:52.237144+00:00
-- url     : https://prove2.me/theorems/b25ca276-4b40-4934-b505-b7d78e7b87f4
-- title:
--   State Event Query
-- statement:
--   Definitions and structural lemmas for State Event Query, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateEventQuery.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateRows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
noncomputable def stateTrianglePointsQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (t : Triangle P) (R : StateRows P) : (Fin 3 → Space) × ℕ :=
  let r0 := stateRowQuery (triangleVertex P t 0) R
  let r1 := stateRowQuery (triangleVertex P t 1) R
  let r2 := stateRowQuery (triangleVertex P t 2) R
  let q0 := pointSnapshotQuery lambda (J (triangleVertex P t 0)) r0.1.2
  let q1 := pointSnapshotQuery lambda (J (triangleVertex P t 1)) r1.1.2
  let q2 := pointSnapshotQuery lambda (J (triangleVertex P t 2)) r2.1.2
  (![q0.1,q1.1,q2.1],r0.2+r1.2+r2.2+q0.2+q1.2+q2.2+18)
noncomputable def stateTriangleQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (t : Triangle P) (R : StateRows P) (z : Space) : Bool × ℕ :=
  let points := stateTrianglePointsQuery P J lambda t R
  let query := triangleQuery points.1 z 2
  (query.1,points.2+query.2)
noncomputable def stateEventQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r) (R : StateRows P) : Bool × ℕ :=
  let net := gridListQuery K
  let anchor := eventAnchorQuery P J r e
  let query := listAnyQuery (fun g : Grid K =>
    let center := fullCenterQuery P J lambda K anchor.1 g
    let triangles := listAllQuery (fun a : e.val =>
      stateTriangleQuery P J lambda a.val R center.1) (Finset.univ.toList : List e.val)
    (triangles.1,center.2+triangles.2+8)) net.1
  (query.1,net.2+anchor.2+query.2+1)
def stateQueryBudget (n v K : ℕ) : ℕ := fullQueryBudget n K+24*(2*K+1)^3*v
end QEC.Coding.BDL26RandomPerturbation


