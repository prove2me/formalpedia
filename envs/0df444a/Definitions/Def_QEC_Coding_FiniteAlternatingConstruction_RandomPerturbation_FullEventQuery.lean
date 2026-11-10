-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T03:08:14.770111+00:00
-- url     : https://prove2.me/theorems/7059f556-c3fc-4af6-8a54-a0af5ef58107
-- title:
--   Full Event Query
-- statement:
--   Definitions and structural lemmas for Full Event Query, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FullEventQuery.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AnchorQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridEnumerationQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SnapshotQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventQuery
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
noncomputable def fullCenterQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (K : ℕ) (a : Option (Triangle P)) (g : Grid K) : Space × ℕ :=
  match a with
  | none => (0,1)
  | some t => let grid := gridPointQuery K g
              let point := pointSnapshotQuery lambda (J (.x (P.faceX t.1))) grid.1
              (point.1,grid.2+point.2+2)
noncomputable def fullTriangleQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (e : Event P J r) (a : e.val)
    (p : eventSupport P J r e → Space) (center : Space) : Bool × ℕ :=
  let snapshot := triangleSnapshotQuery P J r lambda e a p
  let query := triangleQuery snapshot.1 center 2
  (query.1,snapshot.2+query.2+15)
noncomputable def fullEventQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r)
    (p : eventSupport P J r e → Space) : Bool × ℕ :=
  let net := gridListQuery K
  let anchor := eventAnchorQuery P J r e
  let query := listAnyQuery (fun g : Grid K =>
    let center := fullCenterQuery P J lambda K anchor.1 g
    let triangles := listAllQuery (fun a : e.val =>
      fullTriangleQuery P J r lambda e a p center.1) (Finset.univ.toList : List e.val)
    (triangles.1,center.2+triangles.2+8)) net.1
  (query.1,net.2+anchor.2+query.2+1)
def fullQueryBudget (n K : ℕ) : ℕ :=
  6*(2*K+1)^3+3*(2*K+1)^2+5*(2*K+1)+1+8*n+10+
    (2*K+1)^3*(3*K+65+4*200201)
end QEC.Coding.BDL26RandomPerturbation


