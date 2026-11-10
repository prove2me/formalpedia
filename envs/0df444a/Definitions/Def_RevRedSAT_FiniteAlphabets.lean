-- Prove2me | Definitions.Def_RevRedSAT_FiniteAlphabets
-- name    : RevRedSAT_FiniteAlphabets
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:31.878421+00:00
-- url     : https://prove2.me/theorems/58a1a437-167e-4613-9dab-0a1f244938e4
-- title:
--   Algorithms: Turing machines with finite stack alphabets
-- statement:
--   The paper fixes no machine model; its running times count bit operations (§3, p.27: "Arithmetic is exact and charged in bit operations"; §4.1, p.28: "All algorithms below are uniform, and all polynomial input factors have fixed exponents").
--
--   In this mission an **algorithm** is a bundled multi-stack Turing machine $M$ of Mathlib (`Turing.TM2ComputableAux Bool Bool`) with Boolean input and output alphabets, and its running time on an input word $w$ is the number of steps after which it halts with a given output word (the platform's run predicate `HMBinPacking.OutputsWithin`). The predicate defined here requires that
--
--   $$\text{every stack alphabet } \Gamma_i \text{ of } M \text{ is finite.}$$
--
--   A machine with an infinite stack alphabet could store unbounded data in one cell and do unbounded work per step, so it would not be an algorithm. Every hypothesis and every conclusion of the mission uses the same machine model.
--
--   **Formalization Note** Mathlib's `FinTM2` makes only the input alphabet a `Fintype`; the finiteness of the other stacks is this separate condition, exactly as in the platform's `MainResults.InTime`. A polynomial change of model is absorbed by the polynomial factors and by the classes $2^{o(k)}$, $2^{O(\cdot)}$ of the statements.
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), §3, p.27; §4.1, p.28 (machine model, uniform algorithms)

import Mathlib

set_option autoImplicit false

namespace RevRedSAT

/-- **Every stack alphabet of the machine is finite.**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), §3, p.27 and §4.1, p.28:
"All algorithms below are uniform, and all polynomial input factors have fixed exponents";
"Arithmetic is exact and charged in bit operations".

The paper names no machine model. Algorithms of this mission are Mathlib's bundled multi-stack
Turing machines `Turing.TM2ComputableAux Bool Bool` (Boolean input and output alphabets), run with
`HMBinPacking.OutputsWithin`, i.e. Mathlib's `Turing.TM2OutputsInTime`. A machine counts as an
algorithm only if every one of its stack alphabets is finite.

**Formalization Note** Mathlib's `FinTM2` makes only the input stack alphabet a `Fintype`; a stack
alphabet that is infinite would let one cell hold unbounded data and one step do unbounded work.
This predicate excludes that, exactly as `MainResults.InTime` does. Polynomial changes of machine
model are absorbed by the polynomial factors and by the classes `2^{o(k)}`, `2^{O(·)}` of the
statements. -/
def FiniteAlphabets (M : Turing.TM2ComputableAux Bool Bool) : Prop :=
  ∀ i, Finite (M.tm.Γ i)

end RevRedSAT


