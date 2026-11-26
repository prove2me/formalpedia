-- Prove2me | Definitions.Def_Erdos266_LatticeLemma
-- name    : Erdos266_LatticeLemma
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:38:32.570449+00:00
-- url     : https://prove2.me/theorems/45404d6a-9eb2-5671-b3db-a675d0426f28
-- title:
--   Lattice Lemma
-- statement:
--   Definitions and structural lemmas for Lattice Lemma, from Ben Keene (benkeene/erdos266; Challenge statement adapted under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and README.md)'s pinned Erdos Problem 266: Kovac-Tao disproof of Stolarsky's conjecture on shifted Ahmes series development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/LatticeLemma.lean

module
public import Definitions.Def_Erdos266_SlopeLemma
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace Erdos266
open Finset Matrix
def latticeMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℤ :=
  Matrix.of fun i j => ((j : ℤ) + 1) ^ (d - 1 - (i : ℕ))
end Erdos266


