-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FourTupleEnumeration
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FourTupleEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T03:01:41.780457+00:00
-- url     : https://prove2.me/theorems/cec26120-7862-4adb-a694-eec67443b3cc
-- title:
--   Four Tuple Enumeration
-- statement:
--   Definitions and structural lemmas for Four Tuple Enumeration, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FourTupleEnumeration.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
def fourTuples {A : Type*} (L : List A) : List (List A) :=
  L.flatMap fun a => L.flatMap fun b => L.flatMap fun c => L.map fun d => [a,b,c,d]
end QEC.Coding.BDL26RandomPerturbation


