-- Prove2me | Definitions.Def_LinfContractionFP_firstIndex
-- name    : LinfContractionFP_firstIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:09.189523+00:00
-- url     : https://prove2.me/theorems/480322c4-b2a8-493c-a48f-9aeefde01a18
-- title:
--   First index satisfying a predicate
-- statement:
--   For a predicate $p$ on $\mathbb N$, $\mathrm{firstIndex}(p)$ is the least $m$ with $p(m)$, or $0$ if there is none.
--
--   It gives each `while` loop of the algorithms its exact number of iterations: a loop whose condition first fails at iteration $m$ runs $\mathrm{firstIndex}$ of the negated condition times.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Algorithm 1, line 3, p.6; Algorithm 3, line 4, p.15

import Mathlib

open scoped Classical

namespace LinfContractionFP

/-- The least natural number `m` with `p m`, or `0` if there is none.

**Formalization Note.** Used to give the `while` loops of Algorithms 1 and 3 their exact number
of iterations: a loop `while c(j)` whose condition fails for the first time at iteration `j = m`
runs `firstIndex (fun j => ¬ c j)` times. It is `Nat.find` when a witness exists. -/
noncomputable def firstIndex (p : ℕ → Prop) : ℕ :=
  if h : ∃ m, p m then Nat.find h else 0

end LinfContractionFP


