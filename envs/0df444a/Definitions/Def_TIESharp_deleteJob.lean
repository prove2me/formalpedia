-- Prove2me | Definitions.Def_TIESharp_deleteJob
-- name    : TIESharp_deleteJob
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:58.112699+00:00
-- url     : https://prove2.me/theorems/2f6c361e-2855-44d7-aa74-fb7786401b36
-- title:
--   Deleting a job from a profile
-- statement:
--   For a profile $b$ with $m+1$ jobs and a job $j$, **deleting** $j$ gives the profile with $m$ jobs obtained by removing column $j$ and keeping the other columns in their order. Correspondingly, the retained part of an assignment $A$ of the $m+1$ jobs is its restriction to the other jobs.
--
--   **Formalization Note.** The retained jobs `Fin m` embed into `Fin (m+1)` by `j.succAbove`; the retained assignment is `A ∘ j.succAbove`.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), §4.1, Lemma 4.2, p.14

import Mathlib

set_option autoImplicit false

namespace TIESharp

/-- **Deleting a job** (Li, *Sharp Bounds for Truthful-in-Expectation Scheduling*,
arXiv:2611.05134, §4.1, Lemma 4.2, p.14): from a profile with `m + 1` jobs remove column `j`,
keeping the other columns in their order.

**Formalization Note.** The retained jobs are `Fin m`, embedded into `Fin (m + 1)` by
`j.succAbove`; correspondingly the retained part of an assignment `A : Fin (m+1) → Fin n` is
`A ∘ j.succAbove`. -/
def deleteJob {n m : ℕ} (j : Fin (m + 1)) (b : Fin n → Fin (m + 1) → ℝ) : Fin n → Fin m → ℝ :=
  fun i l => b i (j.succAbove l)

end TIESharp


