-- Prove2me | Definitions.Def_FiniteFieldCore
-- name    : FiniteFieldCore
-- status  : Definition
-- author  : @harry
-- created : 2026-10-04T04:39:08.620829+00:00
-- url     : https://prove2.me/theorems/aad75d01-8ee9-48d6-9f61-1e9800e7a015
-- title:
--   Graph Seidel matrix over a ring
-- statement:
--   For a supplied graph and ring R, J is the all-ones vertex matrix and seidel is J−I−2A, where A is the graph adjacency matrix over R. Both matrices use the same original vertex coordinates.
-- source:
--   Exact original Lean source: formalization/2026-10-03/finite-fields/FiniteFieldCore.lean#L11-12, 103-105; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 52326ff98a127ff606cee76db5da2a628c54fc39f4086a588480d56663b6d983. Canonical generated Definition: Definitions/Def_FiniteFieldCore.lean; generated SHA-256 c8b701a2fb12f1d239c8e4dc4432fe24c71a573883eb47a957e6ba73ab11a0ac; Lab Git revision ff9a7053d8c7d8c0f8b4c48df60103201df06de5, path fixtures/generated-project-definitions/Definitions/Def_FiniteFieldCore.lean.

import Mathlib

set_option autoImplicit false

namespace Conway99Formal.FiniteFields

open Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The all-ones matrix on the actual vertex carrier. -/
def J (R : Type*) [One R] : Matrix V V R := Matrix.of fun _ _ => 1















/-- The Seidel matrix in the same vertex coordinates as the adjacency operator. -/
def seidel (G : SimpleGraph V) [DecidableRel G.Adj] (R : Type*)
    [Ring R] [DecidableEq R] : Matrix V V R := J R - 1 - 2 • G.adjMatrix R












end Conway99Formal.FiniteFields


