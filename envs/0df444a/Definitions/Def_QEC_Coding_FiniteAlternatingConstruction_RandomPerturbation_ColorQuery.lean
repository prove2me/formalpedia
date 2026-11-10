-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T03:03:41.365198+00:00
-- url     : https://prove2.me/theorems/80b7f999-17b3-4d77-b649-eb8c7003ec72
-- title:
--   Color Query
-- statement:
--   Definitions and structural lemmas for Color Query, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ColorQuery.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
def countQuery {A : Type*} (q : A → Bool × ℕ) : List A → ℕ × ℕ
  | [] => (0,0)
  | a::L => let qa := q a; let tail := countQuery q L
            ((if qa.1 then 1 else 0)+tail.1,qa.2+tail.2+1)
noncomputable def fiberRankQuery (P : TannerSquarePresentation) {A : Type*} [DecidableEq A]
    (f : Triangle P → A) (a : Triangle P) : ℕ × ℕ :=
  let rankA := indexQuery a (triangleInputList P)
  let q := countQuery (fun b : Triangle P =>
    let rankB := indexQuery b (triangleInputList P)
    (decide (f b = f a ∧ rankB.1 < rankA.1),rankB.2+4)) (triangleInputList P)
  (q.1,rankA.2+q.2)
noncomputable def triangleColorQuery (P : TannerSquarePresentation) (a : Triangle P) :
    (Fin 3 → ℕ) × ℕ := by
  classical
  let qx := fiberRankQuery P (fun t => P.faceX t.1) a
  let qq := fiberRankQuery P (fun t => P.faceQ t.1 t.2) a
  let qz := fiberRankQuery P (fun t => P.faceZ t.1) a
  exact (![qx.1,qq.1,qz.1],qx.2+qq.2+qz.2)
end QEC.Coding.BDL26RandomPerturbation


