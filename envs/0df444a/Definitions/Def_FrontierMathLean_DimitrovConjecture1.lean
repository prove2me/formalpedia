-- Prove2me | Definitions.Def_FrontierMathLean_DimitrovConjecture1
-- name    : FrontierMathLean_DimitrovConjecture1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T08:41:03.015416+00:00
-- url     : https://prove2.me/theorems/f2614ff6-880b-5511-a170-083bf7d6c21b
-- title:
--   Dimitrov Conjecture1
-- statement:
--   Definitions and structural lemmas for Dimitrov Conjecture1, from Michael Mazur / pro20541 (pro20541/dimitrov-conjectures-lean; see pinned Apache-2.0 LICENSE and PROVENANCE.md)'s pinned Full-range proofs and equality characterizations for Dimitrov's Conjectures 1 and 3 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/DimitrovConjecture1.lean

import Definitions.Def_FrontierMathLean_ThreeTermInequality
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Misc
set_option autoImplicit false
open Finset
open scoped ArithmeticFunction.sigma
namespace FrontierMathLean
def dedekindPsi (n : ℕ) : ℕ :=
  if n = 0 then 0 else
    ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p + 1)
end FrontierMathLean


