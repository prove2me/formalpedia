-- Prove2me | Definitions.Def_SkipListConc_entropy
-- name    : SkipListConc_entropy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:49:55.901287+00:00
-- url     : https://prove2.me/theorems/71b81d96-f821-4f59-b543-13e6e6d6ccad
-- title:
--   Entropy benchmark $\mathrm{Ent}(\sigma)$
-- statement:
--   Let $\sigma$ be an operation sequence of length $F$, and $f_x$ the number of operations on item $x$. With $b=1/p>1$, the **entropy benchmark** is
--   $$
--   \mathrm{Ent}(\sigma)=F+\sum_{x}f_x\log_b\frac{F}{f_x},
--   $$
--   the sum over the distinct items of $\sigma$. A structure whose total cost is within a constant factor of $\mathrm{Ent}(\sigma)$ is statically optimal.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §1.2, p.7

import Mathlib

namespace SkipListConc

/-- The entropy benchmark of an access sequence (Kapoor–Tanveer, *Counter-Free Self-Adjusting
Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c),
§1.2, p.7):
`Ent(σ) = F + ∑_x f_x log_b (F / f_x)`, with `F` the length of `σ`, `f_x` the number of operations
on `x`, the sum over the distinct items of `σ`, and `b = 1/p`. -/
noncomputable def entropy {α : Type*} [DecidableEq α] (p : ℝ) (σ : List α) : ℝ :=
  (σ.length : ℝ) + ∑ x ∈ σ.toFinset,
    (σ.count x : ℝ) * Real.logb (1 / p) ((σ.length : ℝ) / (σ.count x : ℝ))

end SkipListConc


