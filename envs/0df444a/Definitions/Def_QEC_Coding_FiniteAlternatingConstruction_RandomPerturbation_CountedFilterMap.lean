-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedFilterMap
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedFilterMap
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:08:37.20761+00:00
-- url     : https://prove2.me/theorems/86fa8a1f-7478-4fa4-9d9c-be77114e53dc
-- title:
--   Counted Filter Map
-- statement:
--   Definitions and structural lemmas for Counted Filter Map, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedFilterMap.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
def filterMapQuery {A B : Type*} (q : A → Option B × ℕ) : List A → List B × ℕ
  | [] => ([],0)
  | a::L => let qa := q a; let tail := filterMapQuery q L
            ((match qa.1 with | none => tail.1 | some b => b::tail.1),qa.2+tail.2+1)
end QEC.Coding.BDL26RandomPerturbation


