-- Prove2me | Definitions.Def_Bdd_Reduce_Discover
-- name    : Bdd_Reduce_Discover
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T06:55:44.841227+00:00
-- url     : https://prove2.me/theorems/df03fa4d-711d-4fc9-9564-73335288da67
-- title:
--   Discover
-- statement:
--   Definitions and structural lemmas for Discover, from Eshel Yaron and contributors's pinned Correctness of binary decision diagrams for CNF formulas development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/Discover.lean

import Definitions.Def_Bdd_Collect
set_option autoImplicit true
open Pointer
open Bdd
def OBdd.discover_helper : List (Fin m) → Vector (Node n m) m → Vector (List (Fin m)) n → Vector (List (Fin m)) n
  | [], _, I => I
  | head :: tail, v, I => OBdd.discover_helper tail v (I.set v[head].var (head :: I[v[head].var]))
def OBdd.discover (O : OBdd n m) : Vector (List (Fin m)) n :=
  OBdd.discover_helper (Collect.collect O) O.1.heap (Vector.replicate n [])


