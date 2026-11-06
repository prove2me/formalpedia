-- Prove2me | Definitions.Def_TIESharp_Nonneg
-- name    : TIESharp_Nonneg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:47.655291+00:00
-- url     : https://prove2.me/theorems/5cc51387-57fe-49dd-af3f-6687c533b7c3
-- title:
--   Nonnegative type or bid profile $t\in[0,\infty)^{n\times m}$
-- statement:
--   There are $n$ machines and $m$ jobs. A **type profile** (or bid profile) is a matrix $t=(t_{ij})\in[0,\infty)^{n\times m}$: row $t_i$ is machine $i$'s private type and $t_{ij}$ its processing time for job $j$. The predicate says that every entry is nonnegative,
--   $$t_{ij}\ge 0\qquad\text{for all } i\in[n],\ j\in[m].$$
--   Zero entries are allowed; they are essential to the model (a job with a zero-cost machine can be added to any schedule at no cost).
--
--   **Formalization Note.** Machines are `Fin n`, jobs `Fin m` (0-based). Profiles are total functions `Fin n → Fin m → ℝ`; the domain $[0,\infty)^{n\times m}$ is carved out by this predicate, which every statement uses as a hypothesis.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), §2, p.3

import Mathlib

set_option autoImplicit false

namespace TIESharp

/-- A **nonnegative profile** (Li, *Sharp Bounds for Truthful-in-Expectation Scheduling*,
arXiv:2611.05134, §2, p.3): a type or bid profile `t = (t_ij) ∈ [0, ∞)^{n×m}`, row `i` being
machine `i`'s processing times for the `m` jobs.

**Formalization Note.** Machines are `Fin n`, jobs `Fin m` (0-based: the paper's job 1 is `0`).
A profile is a total function `Fin n → Fin m → ℝ`; the paper's domain `[0, ∞)^{n×m}` is carved out
by this predicate, which every statement uses as a hypothesis. Zero entries are allowed. -/
def Nonneg {n m : ℕ} (t : Fin n → Fin m → ℝ) : Prop :=
  ∀ i j, 0 ≤ t i j

end TIESharp


