-- Prove2me | Definitions.Def_Sabidussi_LocalPattern
-- name    : Sabidussi_LocalPattern
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:07:27.265189+00:00
-- url     : https://prove2.me/theorems/d0854278-da94-5a07-ba88-5d23511f478d
-- title:
--   Local Pattern
-- statement:
--   Definitions and structural lemmas for Local Pattern, from Upstream contributors (gexahedron/sabidussi-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Sabidussi compatibility conjecture for finite Eulerian loop multigraphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LocalPattern.lean

import Definitions.Def_Sabidussi_Color
set_option autoImplicit true
namespace Sabidussi
open scoped BigOperators
def choiceColor (c : Fin 3) : Color := tripleDifference (1, 0) c
def localDifference : (n : ℕ) → Fin 3 → Fin (n + 2) → Color
  | 0, c => doubleDifference (choiceColor c)
  | 1, c => tripleDifference (choiceColor c)
  | n + 2, c =>
      Fin.cases (choiceColor c) (Fin.cases (choiceColor c) (localDifference n c))
end Sabidussi


