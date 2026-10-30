-- Prove2me | Definitions.Def_LindenReversibility_Protocol
-- name    : LindenReversibility_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:16:35.179293+00:00
-- url     : https://prove2.me/theorems/ef5d0878-9695-42ee-ba3c-d045ee12125f
-- title:
--   Local protocol of three parties (a finite tree of local measurements)
-- statement:
--   A **local protocol** of Alice, Bob and Claire is a finite tree. Each node is either a leaf ("stop") or a step in which one party applies a finite family of operators $K_1,\dots,K_n$ to their own system; the outcome $k$ is communicated to everybody and the protocol continues with a sub-protocol chosen for that outcome. Later steps, by any party, may therefore depend on all earlier outcomes.
--
--   This is the paper's setting: "Alice, Bob and Claire share a pure state. They are allowed to perform local operations and classical communication … The state of the system branches according to the outcome of any measurements performed, but at each stage the state in a given branch is still pure" (p.2), over "many rounds of local measurement, classical communication and unitary transformations" (p.3).
--
--   **Formalization Note** The step operators are arbitrary matrices in this definition; that each step is a complete family of measurement operators is the separate predicate `Protocol.IsLocal`. No branch is coarse-grained and no subsystem is discarded, as on p.2.
-- source:
--   Linden, Popescu, Schumacher, Westmoreland, Reversibility of local transformations of multiparticle entanglement, arXiv:quant-ph/9912039v1, p.2 (model, "It will simplify matters…") and p.3 (sentence before (22))

import Mathlib

universe u v w

namespace LindenReversibility

/-- Linden, Popescu, Schumacher, Westmoreland, arXiv:quant-ph/9912039v1, p.2 ("Alice, Bob and
Claire share a pure state. They are allowed to perform local operations and classical
communication … The state of the system branches according to the outcome of any measurements
performed, but at each stage the state in a given branch is still pure") and p.3 ("an extended
protocol in which Alice, Bob and Claire perform many rounds of local measurement, classical
communication and unitary transformations"): a local protocol of three parties, as a finite tree.

`stop` ends a branch. `stepA n K next` lets Alice apply the measurement operators
`K i` (`i : Fin n`) on her system `A`; the outcome `i` is broadcast and the protocol continues with
`next i` (so later steps, by anybody, may depend on all earlier outcomes). `stepB`, `stepC` are
the same for Bob (system `B`) and Claire (system `C`).

**Formalization Note.** The operators of a step are arbitrary matrices here; the completeness
condition is `Protocol.IsLocal`. Every branch is kept (no outcomes are forgotten) and no subsystem
is discarded, as on p.2. -/
inductive Protocol (A : Type u) (B : Type v) (C : Type w) : Type (max u v w) where
  /-- The branch ends. -/
  | stop : Protocol A B C
  /-- Alice applies the measurement operators `K`, then the protocol continues with `next i`. -/
  | stepA (n : ℕ) (K : Fin n → Matrix A A ℂ) (next : Fin n → Protocol A B C) : Protocol A B C
  /-- Bob applies the measurement operators `K`, then the protocol continues with `next i`. -/
  | stepB (n : ℕ) (K : Fin n → Matrix B B ℂ) (next : Fin n → Protocol A B C) : Protocol A B C
  /-- Claire applies the measurement operators `K`, then the protocol continues with `next i`. -/
  | stepC (n : ℕ) (K : Fin n → Matrix C C ℂ) (next : Fin n → Protocol A B C) : Protocol A B C

end LindenReversibility


