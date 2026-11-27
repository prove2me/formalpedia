-- Prove2me | Definitions.Def_SizeRamsey_SmallGraphs
-- name    : SizeRamsey_SmallGraphs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:18:55.067683+00:00
-- url     : https://prove2.me/theorems/84d2ddbc-9b90-53d4-b59c-05ceed555b74
-- title:
--   Small Graphs
-- statement:
--   Definitions and structural lemmas for Small Graphs, from benkeene (benkeene/size-ramsey; see pinned Apache-2.0 LICENSE and source headers)'s pinned Connected size-Ramsey number of a four-edge matching versus a quadrilateral equals 17 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean

module
public import Definitions.Def_SizeRamsey_FiniteChecks
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace SizeRamsey.Plan
open scoped BigOperators
universe u v
section Certificates
def cycle4Pres : Fin 4 → Finset (Fin 4) := fun v => {v}
def wheel5Pres : Fin 5 → Finset (Fin 5) := ![{0, 4}, {1, 4}, {2, 4}, {3, 4}, {4, 0}]
def k33Pres : Fin 6 → Finset (Fin 6) := ![{0, 1}, {1, 2}, {2, 0}, {3, 4}, {4, 5}, {5, 3}]
def octahedronPres : Fin 6 → Finset (Fin 6) :=
  ![{0, 1, 2}, {1, 0, 2}, {2, 3, 0}, {3, 2, 0}, {4, 5, 0}, {5, 4, 0}]
end Certificates
attribute [local instance] Classical.propDecidable
end SizeRamsey.Plan


