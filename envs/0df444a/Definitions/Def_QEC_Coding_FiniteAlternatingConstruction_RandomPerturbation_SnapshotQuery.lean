-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SnapshotQuery
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SnapshotQuery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T02:59:51.436448+00:00
-- url     : https://prove2.me/theorems/8588469e-e884-48d0-b6f5-997d3baa96f6
-- title:
--   Snapshot Query
-- statement:
--   Definitions and structural lemmas for Snapshot Query, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SnapshotQuery.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add

set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
noncomputable def snapshotCoordinateExpr (lambda : ℝ) (j : Fin 3) : RealExpr :=
  .add (.mul (.constant lambda) (.mul (.constant (1/2)) (.vertex 0 j))) (.vertex 1 j)
noncomputable def pointSnapshotQuery (lambda : ℝ) (a b : Space) : Space × ℕ :=
  let q0 := (snapshotCoordinateExpr lambda 0).run ![a,b,0] 0 0
  let q1 := (snapshotCoordinateExpr lambda 1).run ![a,b,0] 0 0
  let q2 := (snapshotCoordinateExpr lambda 2).run ![a,b,0] 0 0
  (WithLp.toLp 2 ![q0.1,q1.1,q2.1],q0.2+q1.2+q2.2+3)
noncomputable def triangleSnapshotQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (e : Event P J r) (a : e.val)
    (p : eventSupport P J r e → Space) : (Fin 3 → Space) × ℕ :=
  let q0 := pointSnapshotQuery lambda (J (triangleVertex P a.val 0)) (p (eventVertex P J r e a 0))
  let q1 := pointSnapshotQuery lambda (J (triangleVertex P a.val 1)) (p (eventVertex P J r e a 1))
  let q2 := pointSnapshotQuery lambda (J (triangleVertex P a.val 2)) (p (eventVertex P J r e a 2))
  (![q0.1,q1.1,q2.1],q0.2+q1.2+q2.2+3)
noncomputable def centerSnapshotQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r) (g : Grid K) : Space × ℕ :=
  pointSnapshotQuery lambda (J (.x (P.faceX (eventAnchor P J r e).1))) (gridPoint K g)
end QEC.Coding.BDL26RandomPerturbation


