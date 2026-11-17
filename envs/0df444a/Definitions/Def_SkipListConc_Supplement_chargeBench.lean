-- Prove2me | Definitions.Def_SkipListConc_Supplement_chargeBench
-- name    : SkipListConc_Supplement_chargeBench
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:47:29.787456+00:00
-- url     : https://prove2.me/theorems/acaff4c8-ce0b-4a2d-b1b8-e1a88d93ad0c
-- title:
--   Benchmark cost $a_t=1+\log_b(t/f_{x_t}(t))$ of one charge
-- statement:
--   Fix $0<p<1$ and $b=1/p$. For an operation sequence $\sigma$ and the charge (search) at time $t$, let $f_{x_t}(t)$ be the number of operations on the target $x_t$ up to and including time $t$. The **benchmark cost** of the charge is
--   $$
--   a_t \;=\; 1+\log_b\frac{t}{f_{x_t}(t)} .
--   $$
--   Here $t/f_{x_t}(t)$ is one over the empirical frequency of $x_t$ at time $t$, so $a_t$ is the cost the entropy benchmark assigns to the charge. It is the scale of the single-search tail bound (Theorem A).
--
--   **Formalization Note** Positions are 0-based: position $t$ is the paper's time $t+1$, so $a=1+\log_b\bigl((t+1)/(\mathrm{opCount}+1)\bigr)$ with $\mathrm{opCount}+1=f_{x_t}(t)$.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §1.2, p.7

import Mathlib
import Definitions.Def_SkipListConc_opCount

namespace SkipListConc.Supplement

/-- The benchmark cost `a_t = 1 + log_b(t / f_{x_t}(t))` of the charge at time `t` (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), §1.2, p.7), with `b = 1/p` and `f_{x_t}(t)` the number of operations on
`x_t` up to and including time `t`.

**Formalization Note** Positions are 0-based: position `t` is the paper's time `t + 1`, so
`a = 1 + log_b((t + 1) / (opCount σ x_t t + 1))`, where `opCount σ x_t t + 1 = f_{x_t}(t)`. -/
noncomputable def chargeBench {α : Type*} [DecidableEq α] (p : ℝ) (σ : List α)
    (t : Fin σ.length) : ℝ :=
  1 + Real.logb (1 / p) (((t : ℕ) + 1 : ℝ) / ((opCount σ (σ.get t) t : ℝ) + 1))

end SkipListConc.Supplement


