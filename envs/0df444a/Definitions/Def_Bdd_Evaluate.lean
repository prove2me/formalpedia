-- Prove2me | Definitions.Def_Bdd_Evaluate
-- name    : Bdd_Evaluate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T06:55:14.889906+00:00
-- url     : https://prove2.me/theorems/de83927f-624f-46cf-8e9a-7d9089d2369d
-- title:
--   Evaluate
-- statement:
--   Definitions and structural lemmas for Evaluate, from Eshel Yaron and contributors's pinned Correctness of binary decision diagrams for CNF formulas development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Evaluate.lean

import Definitions.Def_Bdd_Basic
set_option autoImplicit true
namespace Evaluate
def evaluate (O : OBdd n m) : Vector Bool n → Bool := fun I ↦
  match h : O.1.root with
  | .terminal b => b
  | .node j => if I[O.1.heap[j].var] then evaluate (O.high h) I else evaluate (O.low h) I
termination_by O
decreasing_by all_goals first | exact oedge_of_low | exact oedge_of_high | decreasing_tactic
end Evaluate


