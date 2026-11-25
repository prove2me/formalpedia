-- Prove2me | Definitions.Def_Erdos935Palomar_Solution
-- name    : Erdos935Palomar_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T12:34:10.912064+00:00
-- url     : https://prove2.me/theorems/8173d79d-c0de-582f-9063-ec4931fd417e
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Daniel Veljjanoski (veljjanoski/erdos935-palomar; statements and definitions reused under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and README.md)'s pinned Erdos Problem 935: powerful parts of products of consecutive integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/veljjanoski/erdos935-palomar/blob/80decbdd1cca367db2185caf5e62acefc28a71d6/Solution.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Filter
namespace Erdos367
def B (r n : ℕ) : ℕ :=
  ∏ i ∈ n.factorization.support with r ≤ n.factorization i, i ^ n.factorization i
end Erdos367
namespace Erdos935Proof
end Erdos935Proof
namespace Erdos935
end Erdos935


