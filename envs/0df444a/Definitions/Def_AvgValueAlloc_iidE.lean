-- Prove2me | Definitions.Def_AvgValueAlloc_iidE
-- name    : AvgValueAlloc_iidE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:38:03.404148+00:00
-- url     : https://prove2.me/theorems/62ba2702-aa10-4ac6-ae1a-9bcde7f47ba9
-- title:
--   Expectation over i.i.d. draws from a finite law
-- statement:
--   For a finite law $D$ with atoms $(p_i,v^{(i)})$, a finite index set $K$ and a function $f$ of a family $(v_k)_{k\in K}$ of items,
--   $$
--   \mathbb E_{v\sim D^{K}} f(v)=\sum_{x:K\to\text{atoms}}\Bigl(\prod_{k\in K}p_{x_k}\Bigr) f\bigl(v^{(x_k)}\bigr)_{k\in K}.
--   $$
--   `iidE` takes values in $[0,\infty]$, `iidR` in $\mathbb R$.
--
--   This is the exact expectation over independent draws used for the live stream, the history, cohorts and service samples.
--
--   **Formalization Note** A finite sum: no measure theory and no integrability side condition.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §1.1, p.2 (independent draws)

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_FinLaw

namespace AvgValueAlloc

open scoped ENNReal

/-- **Expectation over independent draws from a finite law.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §1.1, p.2: "S ≥ 0 historical and T live vectors
are independent draws from an unknown finite-support law D".

For a finite index type `κ` and a function `f` of a family of items indexed by `κ`,
`iidE D κ f = Σ_x (Π_k p(x_k)) · f(val ∘ x)`, the sum over all choices `x` of one atom per index:
the expectation of `f` when the items are independent draws from `D`. `iidE` takes values in
`ℝ≥0∞`, `iidR` is the same sum in `ℝ`.

**Formalization Note.** An exact finite sum; no measure theory and no integrability side
condition. -/
noncomputable def iidE {n : ℕ} (D : FinLaw n) (κ : Type) [Fintype κ] [DecidableEq κ]
    (f : (κ → Vec n) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ x : κ → D.ι, ENNReal.ofReal (∏ k, D.p (x k)) * f (fun k => D.val (x k))

/-- The same expectation for a real-valued function. -/
noncomputable def iidR {n : ℕ} (D : FinLaw n) (κ : Type) [Fintype κ] [DecidableEq κ]
    (f : (κ → Vec n) → ℝ) : ℝ :=
  ∑ x : κ → D.ι, (∏ k, D.p (x k)) * f (fun k => D.val (x k))

end AvgValueAlloc


