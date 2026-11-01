-- Prove2me | Definitions.Def_ParetoIneff_SingleTaskMech
-- name    : ParetoIneff_SingleTaskMech
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:44.431149+00:00
-- url     : https://prove2.me/theorems/f3e9a57e-53e3-4c21-bb42-1cd01bdefb26
-- title:
--   Single-task mechanism
-- statement:
--   A **single-task mechanism** on $n$ machines takes a vector $s\in\mathbb R_{\ge0}^n$ of reported processing times for one task and returns an allocation and a payment vector. The allocation $x(s)\in\{0,1\}^n$ with $\sum_i x_i(s)=1$ names the machine that receives the task; the payment $p_i(s)\ge0$ is what machine $i$ is paid.
--
--   These are the components $\mathcal A_j$ of a task-independent mechanism, and every equilibrium statement about a single task is phrased with them.
--
--   **Formalization Note** Machines are `Fin n`, and the allocation is stored as the receiving machine.
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, §2, p.5 and Definition 1, p.6

import Mathlib

open NNReal

namespace ParetoIneff

/-- A **(deterministic, direct-revelation) single-task mechanism** `A = (x, p)` on `n` machines,
Filos-Ratsikas, Giannakopoulos, Lazos, *The Pareto frontier of inefficiency in mechanism design*,
arXiv:1809.03454v7, §2, p.5 (with one task) and Definition 1, p.6 (the components `𝒜_j`).

Given the vector `s ∈ ℝ≥0ⁿ` of reported processing times for the task, `alloc s` is the machine
that receives the task and `pay s i ∈ ℝ≥0` is the payment to machine `i`.

**Formalization Note** Machines are `Fin n` (0-based). The allocation `x(s) ∈ {0,1}ⁿ` with
`∑ᵢ xᵢ(s) = 1` is encoded as the single machine `alloc s` with `xᵢ(s) = 1` iff `i = alloc s`.
Reports are in `ℝ≥0`, the paper's strategy space. -/
structure SingleTaskMech (n : ℕ) where
  /-- The machine that receives the task at the reported vector. -/
  alloc : (Fin n → ℝ≥0) → Fin n
  /-- The payment to each machine at the reported vector. -/
  pay : (Fin n → ℝ≥0) → Fin n → ℝ≥0

end ParetoIneff


