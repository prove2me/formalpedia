-- Prove2me | Definitions.Def_TIESharp_opt
-- name    : TIESharp_opt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:54.900704+00:00
-- url     : https://prove2.me/theorems/bd29ecfa-b09c-4f0d-9674-1f52a87dd967
-- title:
--   Minimum makespan $\mathrm{OPT}(t)$ over integral assignments
-- statement:
--   An **assignment** $A:[m]\to[n]$ places each job on one machine. Machine $i$'s load is $L_i(t,A)=\sum_{j:A(j)=i}t_{ij}$, the makespan is $C_{\max}(t,A)=\max_{i\in[n]}L_i(t,A)$, and the minimum makespan over all integral assignments is
--   $$\mathrm{OPT}(t)=\min_{A\in\mathcal A_{m,n}} C_{\max}(t,A),\qquad \mathcal A_{m,n}=\{A:[m]\to[n]\}.$$
--   It is the benchmark against which every mechanism is measured.
--
--   **Formalization Note.** Loads and makespans are the published `MatousekLP.Scheduling.load` and `makespan` (machines × jobs orientation; the profile is `Matrix.of t`). The minimum is `⨅` over the finite type `Fin m → Fin n`, nonempty whenever $n\ge1$; with no jobs, $\mathrm{OPT}=0$.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), §2, p.3

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule

set_option autoImplicit false

namespace TIESharp

/-- The **minimum makespan** over all integral assignments (Li, *Sharp Bounds for
Truthful-in-Expectation Scheduling*, arXiv:2611.05134, §2, p.3):
`OPT(t) = min_{A ∈ A_{m,n}} C_max(t, A)`, with `C_max(t, A) = max_i Σ_{j : A(j) = i} t_ij`.

**Formalization Note.** Loads and makespan are the published
`MatousekLP.Scheduling.load` / `makespan` (machines × jobs orientation, so the profile
`t : Fin n → Fin m → ℝ` is the matrix `Matrix.of t`). The minimum is `⨅` over the finite type
`Fin m → Fin n` of assignments, which is nonempty whenever `n ≥ 1` (every statement using `opt`
has `n ≥ 1`); for `m = 0` the unique empty assignment gives `opt t = 0`. -/
noncomputable def opt {n m : ℕ} (t : Fin n → Fin m → ℝ) : ℝ :=
  ⨅ A : Fin m → Fin n, MatousekLP.Scheduling.makespan (Matrix.of t) A

end TIESharp


