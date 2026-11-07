-- Prove2me | Definitions.Def_AvgValueAlloc_OPTon
-- name    : AvgValueAlloc_OPTon
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:38:59.234764+00:00
-- url     : https://prove2.me/theorems/4ba61000-206f-4d9c-9a07-b2249582e63c
-- title:
--   Law-known causal optimum $\mathrm{OPT}_{\mathrm{on}}(D,T)$
-- statement:
--   For thresholds $\rho$, a finite law $D$ and horizon $T$,
--   $$
--   \mathrm{OPT}_{\mathrm{on}}(D,T)=\sup_{\pi}\ \mathbb E_{v\sim D^T}\, W\bigl(v,\pi(v)\bigr),
--   $$
--   the supremum over causal policies $\pi$ that satisfy (1) on every live sequence: the optimal expected welfare of a computationally unbounded causal policy that knows $D$ but not future draws.
--
--   It is the benchmark of the first row of Table 1.
--
--   **Formalization Note** Values in $[0,\infty]$. A policy feasible only on sequences in the support becomes everywhere feasible, with the same expected welfare, by rejecting violating moves.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §1.1, p.2

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_FinLaw
import Definitions.Def_AvgValueAlloc_iidE
import Definitions.Def_AvgValueAlloc_welfare
import Definitions.Def_AvgValueAlloc_prefixFeasible
import Definitions.Def_AvgValueAlloc_Policy

namespace AvgValueAlloc

open scoped ENNReal

/-- **The law-known causal optimum `OPT_on(D, T)`.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §1.1, p.2: "OPT_on(D, T) is optimal expected
welfare of a computationally unbounded causal policy knowing D, not future draws, under (1)."

`OPTon ρ D T = sup_π E_{v ∼ D^T} welfare(v, π(v))`, the supremum over all deterministic causal
policies `π` that satisfy (1) on every live sequence.

**Formalization Note.** Values in `ℝ≥0∞`, so the supremum is never a junk value. A policy
feasible only on sequences in the support of `D` becomes everywhere feasible, with the same
expected welfare, by rejecting every move that would violate (1); hence the "every sequence"
quantifier does not change the value. -/
noncomputable def OPTon {n : ℕ} (ρ : Fin n → ℚ) (D : FinLaw n) (T : ℕ) : ℝ≥0∞ :=
  ⨆ (π : Policy n) (_ : ∀ vs : Fin T → Vec n, prefixFeasible ρ vs (π.run vs)),
    iidE D (Fin T) (fun vs => ENNReal.ofReal (welfare vs (π.run vs)))

end AvgValueAlloc


