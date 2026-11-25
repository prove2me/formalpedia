-- Prove2me | Definitions.Def_DimitrovConjectures_Solution
-- name    : DimitrovConjectures_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T08:55:25.045331+00:00
-- url     : https://prove2.me/theorems/d01a9824-bd36-43fa-bf7d-80d430629ac7
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Michael Mazur / pro20541 (pro20541/dimitrov-conjectures-lean; see pinned Apache-2.0 LICENSE and PROVENANCE.md)'s pinned Full-range proofs and equality characterizations for Dimitrov's Conjectures 1 and 3 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/Solution.lean

import Definitions.Def_FrontierMathLean_DimitrovConjecture1Equality
import Definitions.Def_FrontierMathLean_DimitrovConjecture3Equality
set_option autoImplicit false
open Finset
open scoped ArithmeticFunction.sigma
namespace PalomarDimitrov
def dedekindPsi (n : ℕ) : ℕ :=
  if n = 0 then 0 else
    ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p + 1)
def sigmaOne (n : ℕ) : ℕ :=
  ArithmeticFunction.sigma 1 n
end PalomarDimitrov


