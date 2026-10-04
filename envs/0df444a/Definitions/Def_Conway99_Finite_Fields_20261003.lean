-- Prove2me | Definitions.Def_Conway99_Finite_Fields_20261003
-- name    : Conway99_Finite_Fields_20261003
-- status  : Definition
-- author  : @harry
-- created : 2026-10-03T18:35:21.819033+00:00
-- url     : https://prove2.me/theorems/80d079da-7850-4f1b-a040-f8ccdfa5f5c3
-- title:
--   Graph-owned all-ones and Seidel matrices for Conway parameters
-- statement:
--   On the literal vertex carrier of a finite simple graph G, define J as the all-ones matrix and seidel G R as J-I-2 times G's adjacency matrix over R. These definitions assert no graph existence.
-- source:
--   Conway99/Conway99/Claims/C04finitefieldranks.lean (SHA-256 dd4045131b6d6eeddb8be571417bf9208ddaac2bc8d6a4019c50313d381c884b); archive/complete-export-2026-10-03/research/mixed_algebra_turn7.md and gram_congruence_turn8.md are inventoried in claims.json but not proved by this checkpoint. Definition source SHA-256 aa40597916105dcb276f16fa5838d1e53c996d80d7c8d3dc1f8edcfda70644d4; standalone proof SHA-256 c0d5b7d40a6207fa7d76b97d9b617232a4fc8f8ba03bcaa5562fb58ba3d8a5fc. These are necessary identities only; the Conway existence problem remains open.

import Mathlib

set_option autoImplicit false

namespace Conway99Formal.FiniteFields

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The all-ones matrix on the actual vertex carrier. -/
def J (R : Type*) [One R] : Matrix V V R := Matrix.of fun _ _ => 1

/-- The Seidel matrix in the same vertex coordinates as the adjacency operator. -/
def seidel (G : SimpleGraph V) [DecidableRel G.Adj] (R : Type*)
    [Ring R] [DecidableEq R] : Matrix V V R := J R - 1 - 2 • G.adjMatrix R

end Conway99Formal.FiniteFields


