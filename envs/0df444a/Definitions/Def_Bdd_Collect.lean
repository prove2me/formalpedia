-- Prove2me | Definitions.Def_Bdd_Collect
-- name    : Bdd_Collect
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T06:55:13.164875+00:00
-- url     : https://prove2.me/theorems/1283cae5-9840-46cb-9c1d-bf71a28aa245
-- title:
--   Collect
-- statement:
--   Definitions and structural lemmas for Collect, from Eshel Yaron and contributors's pinned Correctness of binary decision diagrams for CNF formulas development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Collect.lean

import Definitions.Def_Bdd_Basic
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace Collect
def collect_helper (O : OBdd n m) : Vector Bool m × List (Fin m) → Vector Bool m × List (Fin m) :=
  match h : O.1.root with
  | .terminal _ => id
  | .node j =>
    fun I ↦ if I.1.get j then I else collect_helper (O.high h) (collect_helper (O.low h) ⟨I.1.set j true, j :: I.2⟩)
termination_by O
decreasing_by all_goals first | exact oedge_of_low | exact oedge_of_high | decreasing_tactic
def collect (O : OBdd n m) : List (Fin m) := (collect_helper O ⟨Vector.replicate m false, []⟩).2
end Collect


