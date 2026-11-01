-- Prove2me | Definitions.Def_ParetoIneff_Mech
-- name    : ParetoIneff_Mech
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:45.619502+00:00
-- url     : https://prove2.me/theorems/81a48633-29cb-43d2-9a60-996a8daae850
-- title:
--   Scheduling mechanism on $n$ machines
-- statement:
--   A **(deterministic, direct-revelation) scheduling mechanism** $\mathcal M=(x,p)$ on $n$ machines takes a reported profile $s\in\mathbb R_{\ge0}^{n\times m}$ of processing times and returns an allocation $x(s)\in\{0,1\}^{n\times m}$ with $\sum_{i}x_{i,j}(s)=1$ for every task $j$, and a payment vector $p(s)\in\mathbb R_{\ge0}^n$.
--
--   The Price of Anarchy and the Price of Stability take a supremum over the number of tasks, so a mechanism on $n$ machines is defined for every $m$.
--
--   **Formalization Note** A mechanism is a family indexed by $m$. A profile is a function from machines and tasks to `ℝ≥0`, row $i$ being the reports of machine $i$, and an allocation is a map sending each task to its machine.
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, §2, p.5

import Mathlib

open NNReal

namespace ParetoIneff

/-- A **scheduling mechanism** `ℳ = (x, p)` on `n` machines, arXiv:1809.03454v7, §2, p.5: for every
number `m` of tasks and every reported profile `s ∈ ℝ≥0^{n×m}`, an allocation `x(s)` of the tasks
to the machines and a payment vector `p(s) ∈ ℝ≥0ⁿ`.

**Formalization Note** A profile is `Fin n → Fin m → ℝ≥0`, row `i` being the vector `sᵢ` of
machine `i` (tasks `Fin m`, 0-based). The allocation is a map `Fin m → Fin n` sending each task to
its machine, which is the 0/1 matrix with `∑ᵢ x_{i,j} = 1` for every task `j`. Because the Price of
Anarchy and the Price of Stability (p.5) take a supremum over the number of tasks `m ∈ ℕ`, a
mechanism on `n` machines is a family indexed by `m`. -/
structure Mech (n : ℕ) where
  /-- `alloc m s j` is the machine receiving task `j` at the reported `n × m` profile `s`. -/
  alloc : (m : ℕ) → (Fin n → Fin m → ℝ≥0) → Fin m → Fin n
  /-- `pay m s i` is the payment `pᵢ(s)` to machine `i` at the reported `n × m` profile `s`. -/
  pay : (m : ℕ) → (Fin n → Fin m → ℝ≥0) → Fin n → ℝ≥0

end ParetoIneff


