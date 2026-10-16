-- Prove2me | Definitions.Def_HiringLP_SimUpper_HardInstance
-- name    : HiringLP_SimUpper_HardInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T10:58:46.137745+00:00
-- url     : https://prove2.me/theorems/ce7dae71-c72e-4743-8b1e-0e83747545a0
-- title:
--   p. 30 and App. D.7, p. ec19 — the hard instance: j² type-1 candidates (p = k/j, v = τ + ετ/j) and k type-2 candidates (p = 1, v = τ)
-- statement:
--   Fix integers $k \ge 1$ and $j$, and reals $\varepsilon, \tau$. The **hard instance** of the proof of Theorem 4 has $k$ positions and $n = j^2 + k$ candidates:
--   1. the first $j^2$ candidates are of **type 1**, with $p_i = k/j$ and $v_i = \tau + \delta$, where $\delta = \varepsilon\tau/j$;
--   2. the remaining $k$ candidates are of **type 2**, with $p_i = 1$ and $v_i = \tau$.
--
--   For $k \le j$, $\varepsilon > 0$ and $\tau \in (0,1)$ it is a valid, sorted, $\tau$-bounded instance. Type-1 candidates are many unreliable candidates of slightly higher value, so a value-ordered policy must offer to them first; type-2 candidates fill all positions for sure.
--
--   **Formalization Note.** Type-1 candidates are the indices $0, \dots, j^2 - 1$ of `Fin (j^2 + k)`, so the labels are sorted by value when $\delta \ge 0$. The division $k/j$ is real division; the milestone statements assume $1 \le k \le j$, so $j \ge 1$ and $k/j \in (0,1]$.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 30 (instance before Theorem 4) and App. D.7, p. ec19 (PDF p. 51), first paragraph (δ = ετ/j)

import Mathlib
import Definitions.Def_HiringLP_SimUpper_Model

namespace HiringLP.SimUpper

/-- The instance of the proof of Theorem 4 (p. 30 and App. D.7, p. ec19): `n = j² + k`
candidates; the first `j²` (type 1) have `p_i = k/j` and `v_i = τ + δ` with `δ = ετ/j`, the
remaining `k` (type 2) have `p_i = 1` and `v_i = τ`. -/
noncomputable def hardInstance (k j : ℕ) (ε τ : ℝ) : SimInstance (j ^ 2 + k) where
  k := k
  p := fun i => if i.val < j ^ 2 then (k : ℝ) / j else 1
  v := fun i => if i.val < j ^ 2 then τ + ε * τ / j else τ

end HiringLP.SimUpper


