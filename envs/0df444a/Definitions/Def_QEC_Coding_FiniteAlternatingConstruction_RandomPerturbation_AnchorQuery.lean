-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AnchorQuery
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AnchorQuery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T03:05:41.676176+00:00
-- url     : https://prove2.me/theorems/a1c1ea9e-94c8-4945-92f2-4fb65fd4f4a6
-- title:
--   Anchor Query
-- statement:
--   Definitions and structural lemmas for Anchor Query, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/AnchorQuery.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
noncomputable def lowerTriangleQuery (P : TannerSquarePresentation) (a b : Triangle P) : Triangle P × ℕ :=
  let qa := indexQuery a (triangleInputList P)
  let qb := indexQuery b (triangleInputList P)
  (if qa.1 ≤ qb.1 then a else b,qa.2+qb.2+1)
noncomputable def anchorFoldQuery (P : TannerSquarePresentation) (a : Triangle P) :
    List (Triangle P) → Triangle P × ℕ
  | [] => (a,0)
  | b::L => let lower := lowerTriangleQuery P a b
            let rest := anchorFoldQuery P lower.1 L
            (rest.1,lower.2+rest.2+1)
noncomputable def eventAnchorQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : Event P J r) : Option (Triangle P) × ℕ :=
  match e.val.toList with
  | [] => (none,1)
  | a::L => let q := anchorFoldQuery P a L
            (some q.1,q.2+1)
end QEC.Coding.BDL26RandomPerturbation


