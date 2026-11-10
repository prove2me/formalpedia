-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_InputSize
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_InputSize
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T02:34:02.986886+00:00
-- url     : https://prove2.me/theorems/5ea9d689-ac1c-434e-bd64-71c876888274
-- title:
--   Input Size
-- statement:
--   Definitions and structural lemmas for Input Size, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/InputSize.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26TannerLocalRegularity
def faceRoute (P : TannerSquarePresentation) (f : P.Face) :
    Σ q : P.Q, Σ x : {x : P.X // P.xq x q = true}, XQIncidentFace P ⟨(x.1,q),x.2⟩ :=
  ⟨P.faceQ f 0, ⟨P.faceX f,P.data.faceQ_xq f 0⟩, ⟨f,rfl,0,rfl⟩⟩
end QEC.Coding.BDL26RandomPerturbation


